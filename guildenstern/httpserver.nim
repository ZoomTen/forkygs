## HTTP server, with three operating modes
## 
## see examples/httptest.nim, examples/streamingposttest.nim, and examples/replychunkedtest.nim for examples.
##

from os import sleep, osLastError, osErrorMsg, OSErrorCode
from posix import recv, send, EAGAIN, EWOULDBLOCK, MSG_NOSIGNAL
import httpcore
export httpcore
import strtabs
export strtabs

import guildenserver
export guildenserver

type
  ContentType* = enum
    ## mode of the server
    NoBody
      ## offers slightly faster handling for requests like GET that do not have a body
    Compact
      ## the default mode. Whole request body must fit into the request string (size defined with [bufferlength] parameter), from where it can then be accessed with [getRequest], [isBody] and [getBody] procs
    Streaming ## read the body yourself with the [receiveStream] iterator 

  HttpContext* = ref object of SocketContext
    request*: string
    requestlen*: int64
    uristart*: int64
    urilen*: int64
    methlen*: int64
    bodystart*: int64
    contentlength*: int64
    contentreceived*: int64
    contentdelivered*: int64
    headers*: StringTableRef

  SocketState* = enum
    Fail = -1
    TryAgain = 0
    Progress = 1
    Complete = 2

  HttpServer* = ref object of GuildenServer
    contenttype*: ContentType
    maxheaderlength* = 10000.int64 ## Maximum allowed size for http header part.
    bufferlength* = 100000.int64
      ## Every thread will reserve this much memory, for buffering the incoming request. Must be larger than maxheaderlength.
    sockettimeoutms* = 5000 ## If socket is unresponsive for longer, it will be closed.
    requestCallback*: proc() {.gcsafe, nimcall, raises: [].}
    parserequestline*: bool
      ## If you don't need uri or method, but need max perf, set this to false
    headerfields*: seq[string] ## list of header fields to be parsed 

const
  MSG_DONTWAIT* = when defined(macosx): 0x80.cint else: 0x40.cint
  MSG_MORE* = 0x8000.cint

proc isHttpContext*(): bool =
  return socketcontext is HttpContext

template http*(): untyped =
  ## Casts the socketcontext thread local variable into a HttpContext
  HttpContext(socketcontext)

template server*(): untyped =
  ## Casts the socketcontext.socketdata.server into a HttpServer
  HttpServer(socketcontext.socketdata.server)

{.push checks: off.}

proc checkSocketState*(ret: int): SocketState =
  if unlikely(shuttingdown):
    return Fail
  if likely(ret > 0):
    return Progress
  if unlikely(ret == 0):
    return TryAgain
  let lastError = osLastError().int
  let cause =
    if unlikely(ret == Excepted.int):
      Excepted
    else:
      # https://www-numi.fnal.gov/offline_software/srt_public_context/WebDocs/Errors/unix_system_errors.html
      if lasterror in [EAGAIN.int, EWOULDBLOCK.int]:
        return TryAgain
      elif lasterror in [2, 9]:
        AlreadyClosed
      elif lasterror == 32:
        ConnectionLost
      elif lasterror == 104:
        ClosedbyClient
      else:
        NetErrored
  if cause == Excepted:
    closeSocket(Excepted, getCurrentExceptionMsg())
  else:
    closeSocket(cause, osErrorMsg(OSErrorCode(lastError)))
  return Fail

from std/strutils import find, parseInt, isLowerAscii, toLowerAscii

proc parseMethod*(): bool =
  if unlikely(http.requestlen < 13):
    server.log(WARN, "too short request: " & http.request)
    closeSocket(ProtocolViolated, "")
    return false
  while http.methlen < http.requestlen and http.request[http.methlen] != ' ':
    http.methlen.inc
  if unlikely(http.methlen == http.requestlen):
    server.log(WARN, "http method missing")
    closeSocket(ProtocolViolated, "")
    return false
  if unlikely(
    http.request[0 .. 1] notin ["GE", "PO", "HE", "PU", "DE", "CO", "OP", "TR", "PA"]
  ):
    server.log(WARN, "invalid http method: " & http.request[0 .. 12])
    closeSocket(ProtocolViolated, "")
    return false
  return true

proc parseRequestLine*(): bool {.gcsafe, raises: [].} =
  if not parseMethod():
    return false
  var i = http.methlen + 1
  let start = i
  while i < http.requestlen and http.request[i] != ' ':
    i.inc()
  http.uristart = start
  http.urilen = i - start

  if unlikely(http.requestlen < http.uristart + http.urilen + 9):
    server.log(WARN, "parseRequestLine: no version")
    (closeSocket(ProtocolViolated, ""); return false)

  if unlikely(
    http.request[http.uristart + http.urilen + 1] != 'H' or
      http.request[http.uristart + http.urilen + 8] != '1'
  ):
    server.log(
      WARN,
      "request not HTTP/1.1: " &
        http.request[http.uristart + http.urilen + 1 .. http.uristart + http.urilen + 8],
    )
    (closeSocket(ProtocolViolated, ""); return false)
  server.log(
    DEBUG,
    $server.port & "/" & $http.socketdata.socket & ": " &
      http.request[0 .. http.uristart + http.urilen + 8],
  )
  true

proc getContentLength*(): bool {.raises: [].} =
  const length = "content-length: ".len
  var start = http.request.find("content-length: ")
  if start == -1:
    start = http.request.find("Content-Length: ")
  if start == -1:
    return true
  var i = start + length
  while i < http.requestlen and http.request[i] != '\c':
    i += 1
  if i == http.requestlen:
    return true
  try:
    http.contentlength = parseInt(http.request[start + length ..< i])
    return true
  except:
    closeSocket(ProtocolViolated, "could not parse content-length")
    return false

proc isHeaderreceived*(previouslen, currentlen: int): bool =
  if currentlen < 4:
    return false
  if http.request[currentlen - 4] == '\c' and http.request[currentlen - 3] == '\l' and
      http.request[currentlen - 2] == '\c' and http.request[currentlen - 1] == '\l':
    http.bodystart = currentlen
    return true

  var i =
    if previouslen > 4:
      previouslen - 4
    else:
      previouslen
  while i <= currentlen - 4:
    if http.request[i] == '\c' and http.request[i + 1] == '\l' and
        http.request[i + 2] == '\c' and http.request[i + 3] == '\l':
      http.bodystart = i + 4
      return true
    inc i
  false

proc getUri*(): string {.raises: [].} =
  ## Returns the uri as a string copy
  doAssert(server.parserequestline == true)
  if http.urilen == 0:
    return
  return http.request[http.uristart ..< http.uristart + http.urilen]

proc isUri*(uri: string): bool {.raises: [].} =
  ## Compares the uri without making a string copy
  assert(server.parserequestline)
  if http.urilen != uri.len:
    return false
  for i in 0 ..< http.urilen:
    if http.request[http.uristart + i] != uri[i]:
      return false
  return true

proc startsUri*(uristart: string): bool {.raises: [].} =
  ## Compares the beginning of the uri without making a string copy
  assert(server.parserequestline)
  if http.urilen < uristart.len:
    return false
  for i in 0 ..< uristart.len:
    if http.request[http.uristart + i] != uristart[i]:
      return false
  true

proc getMethod*(): string {.raises: [].} =
  ## Returns the method as a string copy
  assert(server.parserequestline)
  if http.methlen == 0:
    return
  return http.request[0 ..< http.methlen]

proc isMethod*(amethod: string): bool {.raises: [].} =
  ## Compares method without making a string copy
  assert(server.parserequestline)
  if http.methlen != amethod.len:
    return false
  for i in 0 ..< http.methlen:
    if http.request[i] != amethod[i]:
      return false
  true

proc getBodylen*(): int =
  if http.bodystart < 1:
    return 0
  return http.requestlen - http.bodystart

when compiles((var x = 1; var vx: var int = x)):
  ## Returns the body without making a string copy.
  proc getBodyview*(http: HttpContext): openArray[char] =
    assert(server.contenttype == Compact)
    if http.bodystart < 1:
      return http.request.toOpenArray(0, -1)
    else:
      return http.request.toOpenArray(http.bodystart, http.requestlen - 1)

proc getBody*(): string =
  ## Returns the body as a string copy.  When --experimental:views compiler switch is used, there is also getBodyview proc that does not take a copy.
  if unlikely(server.contenttype != Compact):
    server.log(ERROR, "getBody is available only when server.contenttype == Compact")
    return
  if http.bodystart < 1:
    return ""
  return http.request[http.bodystart ..< http.requestlen]

proc isBody*(body: string): bool =
  ## Compares the body without making a string copy
  if unlikely(server.contenttype != Compact):
    server.log(ERROR, "isBody is available only when server.contenttype == Compact")
    return
  let len = http.requestlen - http.bodystart
  if len != body.len:
    return false
  for i in http.bodystart ..< http.bodystart + len:
    if http.request[i] != body[i]:
      return false
  true

proc getRequest*(): string =
  assert(server.contenttype == Compact)
  return http.request[0 ..< http.requestlen]

proc receiveHeader(): bool {.gcsafe, raises: [].} =
  var backoff = 4
  var totalbackoff = 0
  while true:
    if shuttingdown:
      return false
    let ret = recv(
      http.socketdata.socket,
      addr http.request[http.requestlen],
      1 + server.maxheaderlength - http.requestlen,
      MSG_DONTWAIT,
    )
    let state = checkSocketState(ret)
    if state == Fail:
      return false
    if state == SocketState.TryAgain:
      suspend(backoff)
      totalbackoff += backoff
      if totalbackoff > server.sockettimeoutms:
        if http.requestlen == 0:
          closeSocket(TimedOut, "client sent nothing")
        else:
          closeSocket(TimedOut, "didn't receive whole header in time")
        return false
      backoff *= 2
      continue
    totalbackoff = 0
    http.requestlen += ret
    if isHeaderreceived(http.requestlen - ret, http.requestlen):
      break
    if http.requestlen > server.maxheaderlength:
      closeSocket(ProtocolViolated, "maximum allowed header size exceeded")
      return false
  http.contentreceived = http.requestlen - http.bodystart
  true

proc parseHeaders() =
  var value = false
  var current: (string, string) = ("", "")
  var found = 0
  var i = 0
  while i <= http.requestlen - 4:
    case http.request[i]
    of '\c':
      if http.request[i + 1] == '\l' and http.request[i + 2] == '\c' and
          http.request[i + 3] == '\l':
        if http.headers.contains(current[0]):
          http.headers[current[0]] = current[1]
        return
    of ':':
      if value:
        current[1].add(':')
      value = true
    of ' ':
      if value:
        if current[1].len != 0:
          current[1].add(http.request[i])
      else:
        current[0].add(http.request[i])
    of '\l':
      if http.headers.contains(current[0]):
        http.headers[current[0]] = current[1]
        found += 1
        if found == http.headers.len:
          return
      value = false
      current = ("", "")
    else:
      if value:
        current[1].add(http.request[i])
      else:
        current[0].add((http.request[i]).toLowerAscii())
    i.inc

proc readHeader*(): bool {.gcsafe, raises: [].} =
  if not receiveHeader():
    return false
  if server.headerfields.len == 0:
    if server.contenttype == NoBody:
      return true
    return getContentLength()
  parseHeaders()
  if http.headers.hasKey("content-length"):
    try:
      if http.headers["content-length"].len > 0:
        http.contentlength = http.headers["content-length"].parseInt()
    except:
      closeSocket(ProtocolViolated, "non-parseable content-length")
      return false
  true

iterator receiveStream*(): (SocketState, string) {.closure, gcsafe, raises: [].} =
  ## Receives a http request in chunks, yielding the state of operation and a possibly received new chuck on every iteration.
  ## With this, you can receive data incrementally without worries about main memory usage.
  ## See examples/streamingposttest.nim for a concrete working example of how to use this iterator.
  if http.contentlength == 0:
    yield (Complete, "")
  else:
    if http.contentreceived == http.contentlength:
      if server.contenttype == Streaming:
        yield (
          Progress, http.request[http.bodystart ..< http.bodystart + http.contentlength]
        )
      yield (Complete, "")
    else:
      if server.contenttype == Streaming:
        yield (
          Progress,
          http.request[http.bodystart ..< http.bodystart + http.contentreceived],
        )
      var continues = true
      while continues:
        if shuttingdown:
          yield (Fail, "")
          continues = false
        else:
          let recvsize =
            if http.contentlength - http.contentreceived > server.bufferlength:
              server.bufferlength
            else:
              http.contentlength - http.contentreceived
          let position =
            if server.contenttype == Streaming:
              0
            else:
              http.bodystart + http.contentreceived
          let ret: int64 = recv(
            http.socketdata.socket, addr http.request[position], recvsize, MSG_DONTWAIT
          )
          let state = checkSocketState(ret)
          if ret > 0:
            http.contentreceived += ret
          http.requestlen =
            if server.contenttype == Streaming:
              ret
            else:
              http.bodystart + http.contentreceived
          if state == Fail:
            yield (Fail, "")
            continues = false
          elif state == Complete or http.contentlength == http.contentreceived:
            if server.contenttype == Streaming:
              yield (Progress, http.request[0 ..< ret])
            yield (Complete, "")
            continues = false
          elif state == TryAgain:
            yield (TryAgain, "")
          else:
            if server.contenttype == Streaming:
              yield (Progress, http.request[0 ..< ret])
            else:
              yield (Progress, "")

proc receiveToSingleBuffer(): bool =
  var backoff = 4
  var totalbackoff = 0
  for (state, chunk) in receiveStream():
    case state
    of TryAgain:
      suspend(backoff)
      totalbackoff += backoff
      if totalbackoff > server.sockettimeoutms:
        closeSocket(TimedOut, "didn't read all contents from socket")
        return false
      backoff *= 2
      continue
    of Fail:
      return false
    of Progress:
      totalbackoff = 0
      continue
    of Complete:
      return true

{.push hint[DuplicateModuleImport]: off.}
from std/strutils import join
from std/strformat import fmt
{.pop.}

template intermediateflags(): cint =
  MSG_NOSIGNAL + MSG_DONTWAIT + MSG_MORE

template lastflags(): cint =
  MSG_NOSIGNAL + MSG_DONTWAIT

let
  version = "HTTP/1.1 "
  http200string = "200 OK\c\L"
  http200nocontent = "HTTP/1.1 200 OK\c\LContent-Length: 0\c\L\c\L"
  http200nocontentlen = 38
  http204string = "HTTP/1.1 204 No Content\c\L\c\L"
  http204stringlen = 27
  shortdivider* = "\c\L"
  longdivider* = "\c\L\c\L"
  contentlen = "Content-Length: "
  zerocontent = "Content-Length: 0\c\L"

proc replyFinish*(): SocketState {.discardable, inline, gcsafe, raises: [].} =
  # Informs that everything is replied.
  let ret =
    try:
      send(http.socketdata.socket, nil, 0, lastflags)
    except CatchableError:
      Excepted.int
  if likely(ret != -1):
    return Complete
  discard checkSocketState(-1)
  return Fail

proc writeToSocket(
    text: ptr string, length: int, flags = intermediateflags
): SocketState {.inline, gcsafe, raises: [].} =
  if length == 0:
    return Complete
  var bytessent = 0
  var backoff = 1
  var totalbackoff = 0
  while true:
    let ret = send(
      http.socketdata.socket,
      unsafeAddr text[bytessent],
      (length - bytessent).cint,
      flags,
    )
    if likely(ret > 0):
      bytessent.inc(ret)
      if bytessent == length:
        server.log(
          DEBUG, "writeToSocket " & $http.socketdata.socket & ": " & text[0 ..< length]
        )
        return Complete
      continue
    result = checkSocketState(ret)
    if result == TryAgain:
      #[
      suspend(backoff)
      totalbackoff += backoff
      backoff *= 2
      if totalbackoff > server.sockettimeoutms:
        closeSocket(TimedOut, "didn't write to socket")
        return Fail
      ]#
      continue
    else:
      return result

proc writeVersion(): SocketState {.inline, gcsafe, raises: [].} =
  {.gcsafe.}:
    return writeToSocket(unsafeAddr version, 9, intermediateflags)

proc writeCode(code: HttpCode): SocketState {.inline, gcsafe, raises: [].} =
  if code == Http200:
    {.gcsafe.}:
      return writeToSocket(unsafeAddr http200string, 8, intermediateflags)
  else:
    let codestring = $code & "\c\L" # slow...
    return writeToSocket(unsafeAddr codestring, codestring.len.cint, intermediateflags)

proc tryWriteToSocket(
    text: ptr string, start: int, length: int, flags = intermediateflags
): (SocketState, int) {.inline, gcsafe, raises: [].} =
  assert(text != nil and length > 0)
  result[1] =
    try:
      send(http.socketdata.socket, unsafeAddr text[start], length.cint, flags)
    except CatchableError:
      Excepted.int
  if likely(result[1] > 0):
    if result[1] == length:
      result[0] = Complete
    else:
      result[0] = Progress
  else:
    result[0] = checkSocketState(result[1])

proc reply*(code: HttpCode): SocketState {.discardable, inline, gcsafe, raises: [].} =
  if unlikely(http.socketdata.socket.int in [0, INVALID_SOCKET.int]):
    http.socketdata.server.log(
      INFO, "cannot reply to closed socket " & $http.socketdata.socket.int
    )
    return
  {.gcsafe.}:
    if code == Http200:
      return writeToSocket(unsafeAddr http200nocontent, http200nocontentlen, lastflags)
    elif code == Http204:
      return writeToSocket(unsafeAddr http204string, http204stringlen, lastflags)
    else:
      if unlikely(writeVersion() != Complete):
        return Fail
      if unlikely(writeCode(code) != Complete):
        return Fail
      if unlikely(writeToSocket(unsafeAddr zerocontent, zerocontent.len) != Complete):
        return Fail
      return writeToSocket(unsafeAddr shortdivider, shortdivider.len, lastflags)

proc reply*(
    code: HttpCode,
    body: ptr string,
    lengthstring: string,
    length: int,
    headers: ptr string,
    moretocome: bool,
): SocketState {.gcsafe, raises: [].} =
  ## One-shot reply to a request
  if unlikely(http.socketdata.socket.int in [0, INVALID_SOCKET.int]):
    http.socketdata.server.log(
      INFO, "cannot reply to closed socket " & $http.socketdata.socket.int
    )
    return
  let finalflag = if moretocome: intermediateflags else: lastflags
  {.gcsafe.}:
    if unlikely(writeVersion() != Complete):
      return Fail
    if unlikely(writeCode(code) != Complete):
      return Fail

    if headers != nil and headers[].len > 0:
      if writeToSocket(headers, headers[].len) != Complete:
        return Fail
      if writeToSocket(unsafeAddr shortdivider, shortdivider.len) != Complete:
        return Fail

    if code == Http101 or code == Http304:
      return writeToSocket(unsafeAddr shortdivider, shortdivider.len, lastflags)

    if writeToSocket(unsafeAddr contentlen, contentlen.len) != Complete:
      return Fail
    if writeToSocket(unsafeAddr lengthstring, lengthstring.len) != Complete:
      return Fail
    if writeToSocket(unsafeAddr longdivider, longdivider.len) != Complete:
      return Fail
    return writeToSocket(body, length, finalflag)

proc replyStart*(
    code: HttpCode, contentlength: int, headers: ptr string = nil
): SocketState {.inline, gcsafe, raises: [].} =
  ## Start replying to a request (continue with [replyMore] and [replyFinish]).
  ## If you do not know the content-length yet, use [replyStartChunked] instead.
  if unlikely(http.socketdata.socket.int in [0, INVALID_SOCKET.int]):
    http.socketdata.server.log(
      INFO, "cannot replystart to closed socket " & $http.socketdata.socket.int
    )
    return
  {.gcsafe.}:
    if unlikely(writeVersion() != Complete):
      return Fail
    if unlikely(writeCode(code) != Complete):
      return Fail

    if headers != nil and headers[].len > 0:
      if writeToSocket(headers, headers[].len) != Complete:
        return Fail

    if contentlength < 1:
      return writeToSocket(unsafeAddr longdivider, longdivider.len)

    if headers != nil and headers[].len > 0:
      if unlikely(writeToSocket(unsafeAddr shortdivider, shortdivider.len) != Complete):
        return Fail

    if unlikely(writeToSocket(unsafeAddr contentlen, contentlen.len) != Complete):
      return Fail
    let lengthstring = $contentlength
    if unlikely(writeToSocket(unsafeAddr lengthstring, lengthstring.len) != Complete):
      return Fail
    return writeToSocket(unsafeAddr longdivider, longdivider.len)

proc reply*(
    code: HttpCode, body: ptr string, headers: ptr string
) {.inline, gcsafe, raises: [].} =
  let length =
    if body == nil:
      0
    else:
      body[].len
  if likely(reply(code, body, $length, length, headers, false) == Complete):
    server.log(TRACE, "reply ok")
  else:
    server.log(INFO, $http.socketdata.socket & ": reply failed")

proc reply*(
    code: HttpCode, body: ptr string, headers: openArray[string]
) {.inline, gcsafe, raises: [].} =
  let joinedheaders = headers.join("\c\L")
  reply(code, body, unsafeAddr joinedheaders)

proc replyStart*(
    code: HttpCode, contentlength: int, headers: openArray[string]
): SocketState {.inline, gcsafe, raises: [].} =
  let joinedheaders = headers.join("\c\L")
  replyStart(code, contentlength, unsafeAddr joinedheaders)

proc replyMore*(
    bodypart: ptr string, start: int, partlength: int = -1
): (SocketState, int) {.inline, gcsafe, raises: [].} =
  ## Continuation to [replyStart].
  let length =
    if partlength != -1:
      partlength
    else:
      bodypart[].len
  return tryWriteToSocket(bodypart, start, length)

template reply*(code: HttpCode, headers: openArray[string]) =
  reply(code, nil, headers)

template reply*(body: string) =
  when compiles(unsafeAddr body):
    reply(Http200, unsafeAddr body, nil)
  else:
    {.fatal: "posix.send requires taking pointer to body, but body has no address".}

template reply*(code: HttpCode, body: string) =
  when compiles(unsafeAddr body):
    reply(code, unsafeAddr body, nil)
  else:
    {.fatal: "posix.send requires taking pointer to body, but body has no address".}

template reply*(code: HttpCode, body: string, headers: openArray[string]) =
  when compiles(unsafeAddr body):
    reply(code, unsafeAddr body, headers)
  else:
    {.fatal: "posix.send requires taking pointer to body, but body has no address".}

template reply*(body: string, headers: openArray[string]) =
  when compiles(unsafeAddr body):
    reply(Http200, unsafeAddr body, headers)
  else:
    {.fatal: "posix.send requires taking pointer to body, but body has no address".}

template replyMore*(bodypart: string): bool =
  when compiles(unsafeAddr bodypart):
    replyMore(unsafeAddr bodypart, 0)
  else:
    {.
      fatal:
        "posix.send requires taking pointer to bodypart, but bodypart has no address"
    .}

proc replyStartChunked*(
    code: HttpCode = Http200, headers: openArray[string] = []
): bool =
  ## Starts replying http response as `Transfer-encoding: chunked`.
  ## Mainly for sending dynamic data, where Content-length header cannot be set.
  ## 
  ## Continue response with calls to `replyContinueChunked`.
  ##
  ## End response with `replyContinueChunked`.
  ## 
  ## See examples/replychunkedtest.nim for a concrete example.
  ## 
  return replyStart(code, -1, ["Transfer-Encoding: chunked"]) != Fail

proc replyContinueChunked*(chunk: string): bool =
  var backoff = 4
  var totalbackoff = 0
  var delivered = 0
  try:
    {.gcsafe.}:
      let delimiter = fmt"{chunk.len:X}" & shortdivider
    if writeToSocket(addr delimiter, delimiter.len) == Fail:
      return false
  except:
    return false
  while true:
    if shuttingdown:
      closeSocket()
      return false
    let (state, len) = tryWriteToSocket(addr chunk, delivered, chunk.len - delivered)
    delivered += len
    if state == Fail:
      return false
    elif state == TryAgain:
      suspend(backoff)
      totalbackoff += backoff
      if totalbackoff > server.sockettimeoutms:
        closeSocket(TimedOut, "didn't write a chunk in time")
        return false
      backoff *= 2
      continue
    elif state == Complete or delivered == chunk.len:
      {.gcsafe.}:
        if writeToSocket(addr shortdivider, shortdivider.len) == Fail:
          return false
      return true

proc replyFinishChunked*(): bool {.discardable.} =
  {.gcsafe.}:
    let delimiter = "0" & longdivider
  if writeToSocket(addr delimiter, delimiter.len) == Fail:
    return false
  return replyFinish() != Fail

proc handleHttpThreadInitialization*(gserver: GuildenServer) =
  if socketcontext == nil:
    socketcontext = new HttpContext
  http.request = newString(HttpServer(gserver).bufferlength + 1)
  if HttpServer(gserver).contenttype != NoBody or
      HttpServer(gserver).headerfields.len > 0:
    http.headers = newStringTable()
    for field in HttpServer(gserver).headerfields:
      http.headers[field] = ""
    if not http.headers.contains("content-length"):
      http.headers["content-length"] = ""
  if gserver.threadInitializerCallback != nil:
    gserver.threadInitializerCallback(gserver)

proc prepareHttpContext*(socketdata: ptr SocketData) {.inline.} =
  http.socketdata = socketdata
  http.requestlen = 0
  http.contentlength = 0
  http.uristart = 0
  http.urilen = 0
  http.methlen = 0
  http.bodystart = -1
  if server.headerfields.len > 0:
    try:
      for key in http.headers.keys:
        http.headers[key].setLen(0)
    except:
      echo "header key error, should never happen"

proc initHttpServer*(
    s: HttpServer,
    loglevel: LogLevel,
    parserequestline: bool,
    contenttype: ContentType,
    headerfields: openArray[string],
) =
  s.initialize(loglevel)
  s.contenttype = contenttype
  s.parserequestline = parserequestline
  s.headerfields.add(headerfields)
  if s.internalThreadInitializationCallback == nil:
    s.internalThreadInitializationCallback = handleHttpThreadInitialization

proc handleRequest(data: ptr SocketData) {.gcsafe, nimcall, raises: [].} =
  let socketdata = data[]
  let socketint = socketdata.socket.int
  if unlikely(socketint == -1):
    return
  prepareHttpContext(addr socketdata)
  if not readHeader():
    return
  if server.parserequestline and not parseRequestLine():
    return
  case server.contenttype
  of NoBody:
    server.log(
      DEBUG,
      "Nobody request of length " & $http.requestlen & " read from socket " & $socketint,
    )
  of Compact:
    if http.contentlength > server.bufferlength:
      closeSocket(ProtocolViolated, "content-length larger than bufferlength")
      return
    if not receiveToSingleBuffer():
      server.log(
        DEBUG, "Receiving request to single buffer failed from socket " & $socketint
      )
      return
  of Streaming:
    server.log(
      DEBUG,
      "Started request streaming with chunk of length " & $http.requestlen &
        " from socket " & $socketint,
    )
  {.gcsafe.}:
    server.requestCallback()

{.pop.}

proc newHttpServer*(
    onrequestcallback: proc() {.gcsafe, nimcall, raises: [].},
    loglevel = LogLevel.WARN,
    parserequestline = true,
    contenttype = Compact,
    headerfields: openArray[string] = [],
): HttpServer =
  ## Constructs a new http server. The essential thing here is to set the onrequestcallback proc.
  ## When it is triggered, the [http] thread-local socket context is accessible.
  ## 
  ## If you want to tinker with [maxheaderlength], [bufferlength] or [sockettimeoutms], that is best done
  ## after the server is constructed but before it is started.
  for field in headerfields:
    for c in field:
      if c != '-' and not isLowerAscii(c):
        server.log(ERROR, "Header field not in lower case: " & field)
  result = new HttpServer
  result.initHttpServer(loglevel, parserequestline, contenttype, headerfields)
  result.handlerCallback = handleRequest
  result.requestCallback = onrequestcallback
