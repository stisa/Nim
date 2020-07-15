#
#
#            Nim's Runtime Library
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#


## The compiler depends on the System module to work properly and the System
## module depends on the compiler. Most of the routines listed here use
## special compiler magic.
##
## Each module implicitly imports the System module; it must not be listed
## explicitly. Because of this there cannot be a user-defined module named
## ``system``.
##
## System module
## =============
##
## .. include:: ./system_overview.rst


type
  float* {.magic: Float.}     ## Default floating point type.
  float32* {.magic: Float32.} ## 32 bit floating point type.
  float64* {.magic: Float.}   ## 64 bit floating point type.

# 'float64' is now an alias to 'float'; this solves many problems

type
  char* {.magic: Char.}         ## Built-in 8 bit character type (unsigned).
  string* {.magic: String.}     ## Built-in string type.
  cstring* {.magic: Cstring.}   ## Built-in cstring (*compatible string*) type.
  pointer* {.magic: Pointer.}   ## Built-in pointer type, use the ``addr``
                                ## operator to get a pointer to a variable.

  typedesc* {.magic: TypeDesc.} ## Meta type to denote a type description.

type
  `ptr`*[T] {.magic: Pointer.}   ## Built-in generic untraced pointer type.
  `ref`*[T] {.magic: Pointer.}   ## Built-in generic traced pointer type.

  `nil` {.magic: "Nil".}

  void* {.magic: "VoidType".}    ## Meta type to denote the absence of any type.
  auto* {.magic: Expr.}          ## Meta type for automatic type determination.
  any* = distinct auto           ## Meta type for any supported type.
  untyped* {.magic: Expr.}       ## Meta type to denote an expression that
                                 ## is not resolved (for templates).
  typed* {.magic: Stmt.}         ## Meta type to denote an expression that
                                 ## is resolved (for templates).

include "system/basic_types"


proc compileOption*(option: string): bool {.
  magic: "CompileOption", noSideEffect.}
  ## Can be used to determine an `on|off` compile-time option. Example:
  ##
  ## .. code-block:: Nim
  ##   when compileOption("floatchecks"):
  ##     echo "compiled with floating point NaN and Inf checks"

proc compileOption*(option, arg: string): bool {.
  magic: "CompileOptionArg", noSideEffect.}
  ## Can be used to determine an enum compile-time option. Example:
  ##
  ## .. code-block:: Nim
  ##   when compileOption("opt", "size") and compileOption("gc", "boehm"):
  ##     echo "compiled with optimization for size and uses Boehm's GC"

{.push warning[GcMem]: off, warning[Uninit]: off.}
{.push hints: off.}

proc `or`*(a, b: typedesc): typedesc {.magic: "TypeTrait", noSideEffect.}
  ## Constructs an `or` meta class.

proc `and`*(a, b: typedesc): typedesc {.magic: "TypeTrait", noSideEffect.}
  ## Constructs an `and` meta class.

proc `not`*(a: typedesc): typedesc {.magic: "TypeTrait", noSideEffect.}
  ## Constructs an `not` meta class.


type
  SomeFloat* = float|float32|float64
    ## Type class matching all floating point number types.

  SomeNumber* = SomeInteger|SomeFloat
    ## Type class matching all number types.

proc defined*(x: untyped): bool {.magic: "Defined", noSideEffect, compileTime.}
  ## Special compile-time procedure that checks whether `x` is
  ## defined.
  ##
  ## `x` is an external symbol introduced through the compiler's
  ## `-d:x switch <nimc.html#compiler-usage-compile-time-symbols>`_ to enable
  ## build time conditionals:
  ##
  ## .. code-block:: Nim
  ##   when not defined(release):
  ##     # Do here programmer friendly expensive sanity checks.
  ##   # Put here the normal code

when defined(nimHashOrdinalFixed):
  type
    Ordinal*[T] {.magic: Ordinal.} ## Generic ordinal type. Includes integer,
                                   ## bool, character, and enumeration types
                                   ## as well as their subtypes. See also
                                   ## `SomeOrdinal`.
else:
  # bootstrap <= 0.20.0
  type
    OrdinalImpl[T] {.magic: Ordinal.}
    Ordinal* = OrdinalImpl | uint | uint64

when defined(nimHasRunnableExamples):
  proc runnableExamples*(rdoccmd = "", body: untyped) {.magic: "RunnableExamples".}
    ## A section you should use to mark `runnable example`:idx: code with.
    ##
    ## - In normal debug and release builds code within
    ##   a ``runnableExamples`` section is ignored.
    ## - The documentation generator is aware of these examples and considers them
    ##   part of the ``##`` doc comment. As the last step of documentation
    ##   generation each runnableExample is put in its own file ``$file_examples$i.nim``,
    ##   compiled and tested. The collected examples are
    ##   put into their own module to ensure the examples do not refer to
    ##   non-exported symbols.
    ##
    ## Usage:
    ##
    ## .. code-block:: Nim
    ##   proc double*(x: int): int =
    ##     ## This proc doubles a number.
    ##     runnableExamples:
    ##       ## at module scope
    ##       assert double(5) == 10
    ##       block: ## at block scope
    ##         defer: echo "done"
    ##     result = 2 * x
    ##     runnableExamples "-d:foo -b:cpp":
    ##       import std/compilesettings
    ##       doAssert querySetting(backend) == "cpp"
    ##     runnableExamples "-r:off": ## this one is only compiled
    ##        import std/browsers
    ##        openDefaultBrowser "https://forum.nim-lang.org/"
else:
  template runnableExamples*(doccmd = "", body: untyped) =
    discard

proc declared*(x: untyped): bool {.magic: "Defined", noSideEffect, compileTime.}
  ## Special compile-time procedure that checks whether `x` is
  ## declared. `x` has to be an identifier or a qualified identifier.
  ##
  ## See also:
  ## * `declaredInScope <#declaredInScope,untyped>`_
  ##
  ## This can be used to check whether a library provides a certain
  ## feature or not:
  ##
  ## .. code-block:: Nim
  ##   when not declared(strutils.toUpper):
  ##     # provide our own toUpper proc here, because strutils is
  ##     # missing it.

proc declaredInScope*(x: untyped): bool {.
  magic: "DefinedInScope", noSideEffect, compileTime.}
  ## Special compile-time procedure that checks whether `x` is
  ## declared in the current scope. `x` has to be an identifier.

proc `addr`*[T](x: var T): ptr T {.magic: "Addr", noSideEffect.} =
  ## Builtin `addr` operator for taking the address of a memory location.
  ## Cannot be overloaded.
  ##
  ## See also:
  ## * `unsafeAddr <#unsafeAddr,T>`_
  ##
  ## .. code-block:: Nim
  ##  var
  ##    buf: seq[char] = @['a','b','c']
  ##    p = buf[1].addr
  ##  echo p.repr # ref 0x7faa35c40059 --> 'b'
  ##  echo p[]    # b
  discard

proc unsafeAddr*[T](x: T): ptr T {.magic: "Addr", noSideEffect.} =
  ## Builtin `addr` operator for taking the address of a memory
  ## location. This works even for ``let`` variables or parameters
  ## for better interop with C and so it is considered even more
  ## unsafe than the ordinary `addr <#addr,T>`_.
  ##
  ## **Note**: When you use it to write a wrapper for a C library, you should
  ## always check that the original library does never write to data behind the
  ## pointer that is returned from this procedure.
  ##
  ## Cannot be overloaded.
  discard

when defined(nimNewTypedesc):
  type
    `static`*[T] {.magic: "Static".}
      ## Meta type representing all values that can be evaluated at compile-time.
      ##
      ## The type coercion ``static(x)`` can be used to force the compile-time
      ## evaluation of the given expression ``x``.

    `type`*[T] {.magic: "Type".}
      ## Meta type representing the type of all type values.
      ##
      ## The coercion ``type(x)`` can be used to obtain the type of the given
      ## expression ``x``.
else:
  proc `type`*(x: untyped): typedesc {.magic: "TypeOf", noSideEffect, compileTime.} =
    ## Builtin `type` operator for accessing the type of an expression.
    ## Cannot be overloaded.
    discard

when defined(nimHasTypeof):
  type
    TypeOfMode* = enum ## Possible modes of `typeof`.
      typeOfProc,      ## Prefer the interpretation that means `x` is a proc call.
      typeOfIter       ## Prefer the interpretation that means `x` is an iterator call.

  proc typeof*(x: untyped; mode = typeOfIter): typedesc {.
    magic: "TypeOf", noSideEffect, compileTime.} =
    ## Builtin `typeof` operation for accessing the type of an expression.
    ## Since version 0.20.0.
    discard


const ThisIsSystem = true

proc internalNew*[T](a: var ref T) {.magic: "New", noSideEffect.}
  ## Leaked implementation detail. Do not use.

when true:
  proc new*[T](a: var ref T, finalizer: proc (x: ref T) {.nimcall.}) {.
    magic: "NewFinalize", noSideEffect.}
    ## Creates a new object of type ``T`` and returns a safe (traced)
    ## reference to it in ``a``.
    ##
    ## When the garbage collector frees the object, `finalizer` is called.
    ## The `finalizer` may not keep a reference to the
    ## object pointed to by `x`. The `finalizer` cannot prevent the GC from
    ## freeing the object.
    ##
    ## **Note**: The `finalizer` refers to the type `T`, not to the object!
    ## This means that for each object of type `T` the finalizer will be called!

proc wasMoved*[T](obj: var T) {.magic: "WasMoved", noSideEffect.} =
  ## Resets an object `obj` to its initial (binary zero) value to signify
  ## it was "moved" and to signify its destructor should do nothing and
  ## ideally be optimized away.
  discard

proc move*[T](x: var T): T {.magic: "Move", noSideEffect.} =
  result = x
  wasMoved(x)

type
  range*[T]{.magic: "Range".}         ## Generic type to construct range types.
  array*[I, T]{.magic: "Array".}      ## Generic type to construct
                                      ## fixed-length arrays.
  openArray*[T]{.magic: "OpenArray".} ## Generic type to construct open arrays.
                                      ## Open arrays are implemented as a
                                      ## pointer to the array data and a
                                      ## length field.
  varargs*[T]{.magic: "Varargs".}     ## Generic type to construct a varargs type.
  seq*[T]{.magic: "Seq".}             ## Generic type to construct sequences.
  set*[T]{.magic: "Set".}             ## Generic type to construct bit sets.

when defined(nimUncheckedArrayTyp):
  type
    UncheckedArray*[T]{.magic: "UncheckedArray".}
    ## Array with no bounds checking.
else:
  type
    UncheckedArray*[T]{.unchecked.} = array[0,T]
    ## Array with no bounds checking.

type sink*[T]{.magic: "BuiltinType".}
type lent*[T]{.magic: "BuiltinType".}

proc high*[T: Ordinal|enum|range](x: T): T {.magic: "High", noSideEffect.}
  ## Returns the highest possible value of an ordinal value `x`.
  ##
  ## As a special semantic rule, `x` may also be a type identifier.
  ##
  ## See also:
  ## * `low(T) <#low,T>`_
  ##
  ## .. code-block:: Nim
  ##  high(2) # => 9223372036854775807

proc high*[T: Ordinal|enum|range](x: typedesc[T]): T {.magic: "High", noSideEffect.}
  ## Returns the highest possible value of an ordinal or enum type.
  ##
  ## ``high(int)`` is Nim's way of writing `INT_MAX`:idx: or `MAX_INT`:idx:.
  ##
  ## See also:
  ## * `low(typedesc) <#low,typedesc[T]>`_
  ##
  ## .. code-block:: Nim
  ##  high(int) # => 9223372036854775807

proc high*[T](x: openArray[T]): int {.magic: "High", noSideEffect.}
  ## Returns the highest possible index of a sequence `x`.
  ##
  ## See also:
  ## * `low(openArray) <#low,openArray[T]>`_
  ##
  ## .. code-block:: Nim
  ##  var s = @[1, 2, 3, 4, 5, 6, 7]
  ##  high(s) # => 6
  ##  for i in low(s)..high(s):
  ##    echo s[i]

proc high*[I, T](x: array[I, T]): I {.magic: "High", noSideEffect.}
  ## Returns the highest possible index of an array `x`.
  ##
  ## See also:
  ## * `low(array) <#low,array[I,T]>`_
  ##
  ## .. code-block:: Nim
  ##  var arr = [1, 2, 3, 4, 5, 6, 7]
  ##  high(arr) # => 6
  ##  for i in low(arr)..high(arr):
  ##    echo arr[i]

proc high*[I, T](x: typedesc[array[I, T]]): I {.magic: "High", noSideEffect.}
  ## Returns the highest possible index of an array type.
  ##
  ## See also:
  ## * `low(typedesc[array]) <#low,typedesc[array[I,T]]>`_
  ##
  ## .. code-block:: Nim
  ##  high(array[7, int]) # => 6

proc high*(x: cstring): int {.magic: "High", noSideEffect.}
  ## Returns the highest possible index of a compatible string `x`.
  ## This is sometimes an O(n) operation.
  ##
  ## See also:
  ## * `low(cstring) <#low,cstring>`_

proc high*(x: string): int {.magic: "High", noSideEffect.}
  ## Returns the highest possible index of a string `x`.
  ##
  ## See also:
  ## * `low(string) <#low,string>`_
  ##
  ## .. code-block:: Nim
  ##  var str = "Hello world!"
  ##  high(str) # => 11

proc low*[T: Ordinal|enum|range](x: T): T {.magic: "Low", noSideEffect.}
  ## Returns the lowest possible value of an ordinal value `x`. As a special
  ## semantic rule, `x` may also be a type identifier.
  ##
  ## See also:
  ## * `high(T) <#high,T>`_
  ##
  ## .. code-block:: Nim
  ##  low(2) # => -9223372036854775808

proc low*[T: Ordinal|enum|range](x: typedesc[T]): T {.magic: "Low", noSideEffect.}
  ## Returns the lowest possible value of an ordinal or enum type.
  ##
  ## ``low(int)`` is Nim's way of writing `INT_MIN`:idx: or `MIN_INT`:idx:.
  ##
  ## See also:
  ## * `high(typedesc) <#high,typedesc[T]>`_
  ##
  ## .. code-block:: Nim
  ##  low(int) # => -9223372036854775808

proc low*[T](x: openArray[T]): int {.magic: "Low", noSideEffect.}
  ## Returns the lowest possible index of a sequence `x`.
  ##
  ## See also:
  ## * `high(openArray) <#high,openArray[T]>`_
  ##
  ## .. code-block:: Nim
  ##  var s = @[1, 2, 3, 4, 5, 6, 7]
  ##  low(s) # => 0
  ##  for i in low(s)..high(s):
  ##    echo s[i]

proc low*[I, T](x: array[I, T]): I {.magic: "Low", noSideEffect.}
  ## Returns the lowest possible index of an array `x`.
  ##
  ## See also:
  ## * `high(array) <#high,array[I,T]>`_
  ##
  ## .. code-block:: Nim
  ##  var arr = [1, 2, 3, 4, 5, 6, 7]
  ##  low(arr) # => 0
  ##  for i in low(arr)..high(arr):
  ##    echo arr[i]

proc low*[I, T](x: typedesc[array[I, T]]): I {.magic: "Low", noSideEffect.}
  ## Returns the lowest possible index of an array type.
  ##
  ## See also:
  ## * `high(typedesc[array]) <#high,typedesc[array[I,T]]>`_
  ##
  ## .. code-block:: Nim
  ##  low(array[7, int]) # => 0

proc low*(x: cstring): int {.magic: "Low", noSideEffect.}
  ## Returns the lowest possible index of a compatible string `x`.
  ##
  ## See also:
  ## * `high(cstring) <#high,cstring>`_

proc low*(x: string): int {.magic: "Low", noSideEffect.}
  ## Returns the lowest possible index of a string `x`.
  ##
  ## See also:
  ## * `high(string) <#high,string>`_
  ##
  ## .. code-block:: Nim
  ##  var str = "Hello world!"
  ##  low(str) # => 0

proc shallowCopy*[T](x: var T, y: T) {.noSideEffect, magic: "ShallowCopy".}
  ## Use this instead of `=` for a `shallow copy`:idx:.
  ##
  ## The shallow copy only changes the semantics for sequences and strings
  ## (and types which contain those).
  ##
  ## Be careful with the changed semantics though!
  ## There is a reason why the default assignment does a deep copy of sequences
  ## and strings.

when defined(nimArrIdx):
  # :array|openArray|string|seq|cstring|tuple
  proc `[]`*[I: Ordinal;T](a: T; i: I): T {.
    noSideEffect, magic: "ArrGet".}
  proc `[]=`*[I: Ordinal;T,S](a: T; i: I;
    x: sink S) {.noSideEffect, magic: "ArrPut".}
  proc `=`*[T](dest: var T; src: T) {.noSideEffect, magic: "Asgn".}

  proc arrGet[I: Ordinal;T](a: T; i: I): T {.
    noSideEffect, magic: "ArrGet".}
  proc arrPut[I: Ordinal;T,S](a: T; i: I;
    x: S) {.noSideEffect, magic: "ArrPut".}

  proc `=destroy`*[T](x: var T) {.inline, magic: "Destroy".} =
    ## Generic `destructor`:idx: implementation that can be overridden.
    discard
  proc `=sink`*[T](x: var T; y: T) {.inline, magic: "Asgn".} =
    ## Generic `sink`:idx: implementation that can be overridden.
    shallowCopy(x, y)

type
  HSlice*[T, U] = object   ## "Heterogeneous" slice type.
    a*: T                  ## The lower bound (inclusive).
    b*: U                  ## The upper bound (inclusive).
  Slice*[T] = HSlice[T, T] ## An alias for ``HSlice[T, T]``.

proc `..`*[T, U](a: sink T, b: sink U): HSlice[T, U] {.noSideEffect, inline, magic: "DotDot".} =
  ## Binary `slice`:idx: operator that constructs an interval ``[a, b]``, both `a`
  ## and `b` are inclusive.
  ##
  ## Slices can also be used in the set constructor and in ordinal case
  ## statements, but then they are special-cased by the compiler.
  ##
  ## .. code-block:: Nim
  ##   let a = [10, 20, 30, 40, 50]
  ##   echo a[2 .. 3] # @[30, 40]
  result = HSlice[T, U](a: a, b: b)

proc `..`*[T](b: sink T): HSlice[int, T] {.noSideEffect, inline, magic: "DotDot".} =
  ## Unary `slice`:idx: operator that constructs an interval ``[default(int), b]``.
  ##
  ## .. code-block:: Nim
  ##   let a = [10, 20, 30, 40, 50]
  ##   echo a[.. 2] # @[10, 20, 30]
  result = HSlice[int, T](a: 0, b: b)

when not defined(niminheritable):
  {.pragma: inheritable.}
when not defined(nimunion):
  {.pragma: unchecked.}
when not defined(nimHasHotCodeReloading):
  {.pragma: nonReloadable.}
when defined(hotCodeReloading):
  {.pragma: hcrInline, inline.}
else:
  {.pragma: hcrInline.}

{.push profiler: off.}
let nimvm* {.magic: "Nimvm", compileTime.}: bool = false
  ## May be used only in `when` expression.
  ## It is true in Nim VM context and false otherwise.
{.pop.}

include "system/arithmetics"
include "system/comparisons"

const
  appType* {.magic: "AppType"}: string = ""
    ## A string that describes the application type. Possible values:
    ## `"console"`, `"gui"`, `"lib"`.

include "system/inclrtl"

const NoFakeVars* = defined(nimscript) ## `true` if the backend doesn't support \
  ## "fake variables" like `var EBADF {.importc.}: cint`.

const notJSnotNims = not defined(js) and not defined(nimscript)

when not defined(js) and not defined(nimSeqsV2):
  type
    TGenericSeq {.compilerproc, pure, inheritable.} = object
      len, reserved: int
      when defined(gogc):
        elemSize: int
        elemAlign: int
    PGenericSeq {.exportc.} = ptr TGenericSeq
    # len and space without counting the terminating zero:
    NimStringDesc {.compilerproc, final.} = object of TGenericSeq
      data: UncheckedArray[char]
    NimString = ptr NimStringDesc

when notJSnotNims and not defined(nimSeqsV2):
  template space(s: PGenericSeq): int {.dirty.} =
    s.reserved and not (seqShallowFlag or strlitFlag)

when notJSnotNims and not defined(nimV2):
  include "system/hti"

type
  byte* = uint8 ## This is an alias for ``uint8``, that is an unsigned
                ## integer, 8 bits wide.

  Natural* = range[0..high(int)]
    ## is an `int` type ranging from zero to the maximum value
    ## of an `int`. This type is often useful for documentation and debugging.

  Positive* = range[1..high(int)]
    ## is an `int` type ranging from one to the maximum value
    ## of an `int`. This type is often useful for documentation and debugging.

  RootObj* {.compilerproc, inheritable.} =
    object ## The root of Nim's object hierarchy.
           ##
           ## Objects should inherit from `RootObj` or one of its descendants.
           ## However, objects that have no ancestor are also allowed.
  RootRef* = ref RootObj ## Reference to `RootObj`.


include "system/exceptions"

when defined(js) or defined(nimdoc):
  type
    JsRoot* = ref object of RootObj
      ## Root type of the JavaScript object hierarchy

proc unsafeNew*[T](a: var ref T, size: Natural) {.magic: "New", noSideEffect.}
  ## Creates a new object of type ``T`` and returns a safe (traced)
  ## reference to it in ``a``.
  ##
  ## This is **unsafe** as it allocates an object of the passed ``size``.
  ## This should only be used for optimization purposes when you know
  ## what you're doing!
  ##
  ## See also:
  ## * `new <#new,ref.T,proc(ref.T)>`_

proc sizeof*[T](x: T): int {.magic: "SizeOf", noSideEffect.}
  ## Returns the size of ``x`` in bytes.
  ##
  ## Since this is a low-level proc,
  ## its usage is discouraged - using `new <#new,ref.T,proc(ref.T)>`_ for
  ## the most cases suffices that one never needs to know ``x``'s size.
  ##
  ## As a special semantic rule, ``x`` may also be a type identifier
  ## (``sizeof(int)`` is valid).
  ##
  ## Limitations: If used for types that are imported from C or C++,
  ## sizeof should fallback to the ``sizeof`` in the C compiler. The
  ## result isn't available for the Nim compiler and therefore can't
  ## be used inside of macros.
  ##
  ## .. code-block:: Nim
  ##  sizeof('A') # => 1
  ##  sizeof(2) # => 8

when defined(nimHasalignOf):
  proc alignof*[T](x: T): int {.magic: "AlignOf", noSideEffect.}
  proc alignof*(x: typedesc): int {.magic: "AlignOf", noSideEffect.}

  proc offsetOfDotExpr(typeAccess: typed): int {.magic: "OffsetOf", noSideEffect, compileTime.}

  template offsetOf*[T](t: typedesc[T]; member: untyped): int =
    var tmp {.noinit.}: ptr T
    offsetOfDotExpr(tmp[].member)

  template offsetOf*[T](value: T; member: untyped): int =
    offsetOfDotExpr(value.member)

  #proc offsetOf*(memberaccess: typed): int {.magic: "OffsetOf", noSideEffect.}

when defined(nimtypedescfixed):
  proc sizeof*(x: typedesc): int {.magic: "SizeOf", noSideEffect.}


proc newSeq*[T](s: var seq[T], len: Natural) {.magic: "NewSeq", noSideEffect.}
  ## Creates a new sequence of type ``seq[T]`` with length ``len``.
  ##
  ## This is equivalent to ``s = @[]; setlen(s, len)``, but more
  ## efficient since no reallocation is needed.
  ##
  ## Note that the sequence will be filled with zeroed entries.
  ## After the creation of the sequence you should assign entries to
  ## the sequence instead of adding them. Example:
  ##
  ## .. code-block:: Nim
  ##   var inputStrings : seq[string]
  ##   newSeq(inputStrings, 3)
  ##   assert len(inputStrings) == 3
  ##   inputStrings[0] = "The fourth"
  ##   inputStrings[1] = "assignment"
  ##   inputStrings[2] = "would crash"
  ##   #inputStrings[3] = "out of bounds"

proc newSeq*[T](len = 0.Natural): seq[T] =
  ## Creates a new sequence of type ``seq[T]`` with length ``len``.
  ##
  ## Note that the sequence will be filled with zeroed entries.
  ## After the creation of the sequence you should assign entries to
  ## the sequence instead of adding them.
  ##
  ## See also:
  ## * `newSeqOfCap <#newSeqOfCap,Natural>`_
  ## * `newSeqUninitialized <#newSeqUninitialized,Natural>`_
  ##
  ## .. code-block:: Nim
  ##   var inputStrings = newSeq[string](3)
  ##   assert len(inputStrings) == 3
  ##   inputStrings[0] = "The fourth"
  ##   inputStrings[1] = "assignment"
  ##   inputStrings[2] = "would crash"
  ##   #inputStrings[3] = "out of bounds"
  newSeq(result, len)

proc newSeqOfCap*[T](cap: Natural): seq[T] {.
  magic: "NewSeqOfCap", noSideEffect.} =
  ## Creates a new sequence of type ``seq[T]`` with length zero and capacity
  ## ``cap``.
  ##
  ## .. code-block:: Nim
  ##   var x = newSeqOfCap[int](5)
  ##   assert len(x) == 0
  ##   x.add(10)
  ##   assert len(x) == 1
  discard

when not defined(js):
  proc newSeqUninitialized*[T: SomeNumber](len: Natural): seq[T] =
    ## Creates a new sequence of type ``seq[T]`` with length ``len``.
    ##
    ## Only available for numbers types. Note that the sequence will be
    ## uninitialized. After the creation of the sequence you should assign
    ## entries to the sequence instead of adding them.
    ##
    ## .. code-block:: Nim
    ##   var x = newSeqUninitialized[int](3)
    ##   assert len(x) == 3
    ##   x[0] = 10
    result = newSeqOfCap[T](len)
    when defined(nimSeqsV2):
      cast[ptr int](addr result)[] = len
    else:
      var s = cast[PGenericSeq](result)
      s.len = len

proc len*[TOpenArray: openArray|varargs](x: TOpenArray): int {.
  magic: "LengthOpenArray", noSideEffect.}
  ## Returns the length of an openArray.
  ##
  ## .. code-block:: Nim
  ##   var s = [1, 1, 1, 1, 1]
  ##   echo len(s) # => 5

proc len*(x: string): int {.magic: "LengthStr", noSideEffect.}
  ## Returns the length of a string.
  ##
  ## .. code-block:: Nim
  ##   var str = "Hello world!"
  ##   echo len(str) # => 12

proc len*(x: cstring): int {.magic: "LengthStr", noSideEffect.}
  ## Returns the length of a compatible string. This is sometimes
  ## an O(n) operation.
  ##
  ## **Note:** On the JS backend this currently counts UTF-16 code points
  ## instead of bytes at runtime (not at compile time). For now, if you
  ## need the byte length of the UTF-8 encoding, convert to string with
  ## `$` first then call `len`.
  ##
  ## .. code-block:: Nim
  ##   var str: cstring = "Hello world!"
  ##   len(str) # => 12

proc len*(x: (type array)|array): int {.magic: "LengthArray", noSideEffect.}
  ## Returns the length of an array or an array type.
  ## This is roughly the same as ``high(T)-low(T)+1``.
  ##
  ## .. code-block:: Nim
  ##   var arr = [1, 1, 1, 1, 1]
  ##   echo len(arr) # => 5
  ##   echo len(array[3..8, int]) # => 6

proc len*[T](x: seq[T]): int {.magic: "LengthSeq", noSideEffect.}
  ## Returns the length of a sequence.
  ##
  ## .. code-block:: Nim
  ##   var s = @[1, 1, 1, 1, 1]
  ##   echo len(s) # => 5


proc ord*[T: Ordinal|enum](x: T): int {.magic: "Ord", noSideEffect.}
  ## Returns the internal `int` value of an ordinal value ``x``.
  ##
  ## .. code-block:: Nim
  ##   echo ord('A') # => 65
  ##   echo ord('a') # => 97

proc chr*(u: range[0..255]): char {.magic: "Chr", noSideEffect.}
  ## Converts an `int` in the range `0..255` to a character.
  ##
  ## .. code-block:: Nim
  ##   echo chr(65) # => A
  ##   echo chr(97) # => a


# floating point operations:
proc `+`*(x: float32): float32 {.magic: "UnaryPlusF64", noSideEffect.}
proc `-`*(x: float32): float32 {.magic: "UnaryMinusF64", noSideEffect.}
proc `+`*(x, y: float32): float32 {.magic: "AddF64", noSideEffect.}
proc `-`*(x, y: float32): float32 {.magic: "SubF64", noSideEffect.}
proc `*`*(x, y: float32): float32 {.magic: "MulF64", noSideEffect.}
proc `/`*(x, y: float32): float32 {.magic: "DivF64", noSideEffect.}

proc `+`*(x: float): float {.magic: "UnaryPlusF64", noSideEffect.}
proc `-`*(x: float): float {.magic: "UnaryMinusF64", noSideEffect.}
proc `+`*(x, y: float): float {.magic: "AddF64", noSideEffect.}
proc `-`*(x, y: float): float {.magic: "SubF64", noSideEffect.}
proc `*`*(x, y: float): float {.magic: "MulF64", noSideEffect.}
proc `/`*(x, y: float): float {.magic: "DivF64", noSideEffect.}

proc `==`*(x, y: float32): bool {.magic: "EqF64", noSideEffect.}
proc `<=`*(x, y: float32): bool {.magic: "LeF64", noSideEffect.}
proc `<`  *(x, y: float32): bool {.magic: "LtF64", noSideEffect.}

proc `==`*(x, y: float): bool {.magic: "EqF64", noSideEffect.}
proc `<=`*(x, y: float): bool {.magic: "LeF64", noSideEffect.}
proc `<`*(x, y: float): bool {.magic: "LtF64", noSideEffect.}


include "system/setops"


proc contains*[U, V, W](s: HSlice[U, V], value: W): bool {.noSideEffect, inline.} =
  ## Checks if `value` is within the range of `s`; returns true if
  ## `value >= s.a and value <= s.b`
  ##
  ## .. code-block:: Nim
  ##   assert((1..3).contains(1) == true)
  ##   assert((1..3).contains(2) == true)
  ##   assert((1..3).contains(4) == false)
  result = s.a <= value and value <= s.b

template `in`*(x, y: untyped): untyped {.dirty.} = contains(y, x)
  ## Sugar for `contains`.
  ##
  ## .. code-block:: Nim
  ##   assert(1 in (1..3) == true)
  ##   assert(5 in (1..3) == false)
template `notin`*(x, y: untyped): untyped {.dirty.} = not contains(y, x)
  ## Sugar for `not contains`.
  ##
  ## .. code-block:: Nim
  ##   assert(1 notin (1..3) == false)
  ##   assert(5 notin (1..3) == true)

proc `is`*[T, S](x: T, y: S): bool {.magic: "Is", noSideEffect.}
  ## Checks if `T` is of the same type as `S`.
  ##
  ## For a negated version, use `isnot <#isnot.t,untyped,untyped>`_.
  ##
  ## .. code-block:: Nim
  ##   assert 42 is int
  ##   assert @[1, 2] is seq
  ##
  ##   proc test[T](a: T): int =
  ##     when (T is int):
  ##       return a
  ##     else:
  ##       return 0
  ##
  ##   assert(test[int](3) == 3)
  ##   assert(test[string]("xyz") == 0)
template `isnot`*(x, y: untyped): untyped = not (x is y)
  ## Negated version of `is <#is,T,S>`_. Equivalent to ``not(x is y)``.
  ##
  ## .. code-block:: Nim
  ##   assert 42 isnot float
  ##   assert @[1, 2] isnot enum

when (defined(nimOwnedEnabled) and not defined(nimscript)) or defined(nimFixedOwned):
  type owned*[T]{.magic: "BuiltinType".} ## type constructor to mark a ref/ptr or a closure as `owned`.
else:
  template owned*(t: typedesc): typedesc = t

when defined(nimOwnedEnabled) and not defined(nimscript):
  proc new*[T](a: var owned(ref T)) {.magic: "New", noSideEffect.}
    ## Creates a new object of type ``T`` and returns a safe (traced)
    ## reference to it in ``a``.

  proc new*(t: typedesc): auto =
    ## Creates a new object of type ``T`` and returns a safe (traced)
    ## reference to it as result value.
    ##
    ## When ``T`` is a ref type then the resulting type will be ``T``,
    ## otherwise it will be ``ref T``.
    when (t is ref):
      var r: owned t
    else:
      var r: owned(ref t)
    new(r)
    return r

  proc unown*[T](x: T): T {.magic: "Unown", noSideEffect.}
    ## Use the expression ``x`` ignoring its ownership attribute.

  # This is only required to make 0.20 compile with the 0.19 line.
  template `<//>`*(t: untyped): untyped = owned(t)

else:
  template unown*(x: typed): untyped = x

  proc new*[T](a: var ref T) {.magic: "New", noSideEffect.}
    ## Creates a new object of type ``T`` and returns a safe (traced)
    ## reference to it in ``a``.

  proc new*(t: typedesc): auto =
    ## Creates a new object of type ``T`` and returns a safe (traced)
    ## reference to it as result value.
    ##
    ## When ``T`` is a ref type then the resulting type will be ``T``,
    ## otherwise it will be ``ref T``.
    when (t is ref):
      var r: t
    else:
      var r: ref t
    new(r)
    return r

  # This is only required to make 0.20 compile with the 0.19 line.
  template `<//>`*(t: untyped): untyped = t

template disarm*(x: typed) =
  ## Useful for ``disarming`` dangling pointers explicitly for the
  ## --newruntime. Regardless of whether --newruntime is used or not
  ## this sets the pointer or callback ``x`` to ``nil``. This is an
  ## experimental API!
  x = nil

proc `of`*[T, S](x: typedesc[T], y: typedesc[S]): bool {.magic: "Of", noSideEffect.}
proc `of`*[T, S](x: T, y: typedesc[S]): bool {.magic: "Of", noSideEffect.}
proc `of`*[T, S](x: T, y: S): bool {.magic: "Of", noSideEffect.}
  ## Checks if `x` has a type of `y`.
  ##
  ## .. code-block:: Nim
  ##   assert(FloatingPointDefect of Exception)
  ##   assert(DivByZeroDefect of Exception)

proc cmp*[T](x, y: T): int =
  ## Generic compare proc.
  ##
  ## Returns:
  ## * a value less than zero, if `x < y`
  ## * a value greater than zero, if `x > y`
  ## * zero, if `x == y`
  ##
  ## This is useful for writing generic algorithms without performance loss.
  ## This generic implementation uses the `==` and `<` operators.
  ##
  ## .. code-block:: Nim
  ##  import algorithm
  ##  echo sorted(@[4, 2, 6, 5, 8, 7], cmp[int])
  if x == y: return 0
  if x < y: return -1
  return 1

{.pop.}