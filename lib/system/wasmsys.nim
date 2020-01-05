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
  int* {.magic: Int.}         ## Default integer type; bitwidth depends on
                              ## architecture, but is always the same as a pointer.
  int8* {.magic: Int8.}       ## Signed 8 bit integer type.
  int16* {.magic: Int16.}     ## Signed 16 bit integer type.
  int32* {.magic: Int32.}     ## Signed 32 bit integer type.
  int64* {.magic: Int64.}     ## Signed 64 bit integer type.
  uint* {.magic: UInt.}       ## Unsigned default integer type.
  uint8* {.magic: UInt8.}     ## Unsigned 8 bit integer type.
  uint16* {.magic: UInt16.}   ## Unsigned 16 bit integer type.
  uint32* {.magic: UInt32.}   ## Unsigned 32 bit integer type.
  uint64* {.magic: UInt64.}   ## Unsigned 64 bit integer type.
  float* {.magic: Float.}     ## Default floating point type.
  float32* {.magic: Float32.} ## 32 bit floating point type.
  float64* {.magic: Float.}   ## 64 bit floating point type.

# 'float64' is now an alias to 'float'; this solves many problems

type # we need to start a new type section here, so that ``0`` can have a type
  bool* {.magic: Bool.} = enum ## Built-in boolean type.
    false = 0, true = 1

type
  char* {.magic: Char.}         ## Built-in 8 bit character type (unsigned).
  string* {.magic: String.}     ## Built-in string type.
  cstring* {.magic: Cstring.}   ## Built-in cstring (*compatible string*) type.
  pointer* {.magic: Pointer.}   ## Built-in pointer type, use the ``addr``
                                ## operator to get a pointer to a variable.

  typedesc* {.magic: TypeDesc.} ## Meta type to denote a type description.

const
  on* = true    ## Alias for ``true``.
  off* = false  ## Alias for ``false``.

{.push warning[GcMem]: off, warning[Uninit]: off.}
{.push hints: off.}

proc `or`*(a, b: typedesc): typedesc {.magic: "TypeTrait", noSideEffect.}
  ## Constructs an `or` meta class.

proc `and`*(a, b: typedesc): typedesc {.magic: "TypeTrait", noSideEffect.}
  ## Constructs an `and` meta class.

proc `not`*(a: typedesc): typedesc {.magic: "TypeTrait", noSideEffect.}
  ## Constructs an `not` meta class.

type
  Ordinal*[T] {.magic: Ordinal.} ## Generic ordinal type. Includes integer,
                                 ## bool, character, and enumeration types
                                 ## as well as their subtypes. Note `uint`
                                 ## and `uint64` are not ordinal types for
                                 ## implementation reasons.
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

  SomeSignedInt* = int|int8|int16|int32|int64
    ## Type class matching all signed integer types.

  SomeUnsignedInt* = uint|uint8|uint16|uint32|uint64
    ## Type class matching all unsigned integer types.

  SomeInteger* = SomeSignedInt|SomeUnsignedInt
    ## Type class matching all integer types.

  SomeOrdinal* = int|int8|int16|int32|int64|bool|enum|uint|uint8|uint16|uint32|uint64
    ## Type class matching all ordinal types; however this includes enums with
    ## holes.

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

when defined(nimHasRunnableExamples):
  proc runnableExamples*(body: untyped) {.magic: "RunnableExamples".}
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
    ##
    ##     result = 2 * x
else:
  template runnableExamples*(body: untyped) =
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

proc `not`*(x: bool): bool {.magic: "Not", noSideEffect.}
  ## Boolean not; returns true if ``x == false``.

proc `and`*(x, y: bool): bool {.magic: "And", noSideEffect.}
  ## Boolean ``and``; returns true if ``x == y == true`` (if both arguments
  ## are true).
  ##
  ## Evaluation is lazy: if ``x`` is false, ``y`` will not even be evaluated.
proc `or`*(x, y: bool): bool {.magic: "Or", noSideEffect.}
  ## Boolean ``or``; returns true if ``not (not x and not y)`` (if any of
  ## the arguments is true).
  ##
  ## Evaluation is lazy: if ``x`` is true, ``y`` will not even be evaluated.
proc `xor`*(x, y: bool): bool {.magic: "Xor", noSideEffect.}
  ## Boolean `exclusive or`; returns true if ``x != y`` (if either argument
  ## is true while the other is false).

const ThisIsSystem = true

proc internalNew*[T](a: var ref T) {.magic: "New", noSideEffect.}
  ## Leaked implementation detail. Do not use.

when not defined(gcDestructors):
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
    x: S) {.noSideEffect, magic: "ArrPut".}
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

proc `..`*[T, U](a: T, b: U): HSlice[T, U] {.noSideEffect, inline, magic: "DotDot".} =
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

proc `..`*[T](b: T): HSlice[int, T] {.noSideEffect, inline, magic: "DotDot".} =
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

# comparison operators:
proc `==`*[Enum: enum](x, y: Enum): bool {.magic: "EqEnum", noSideEffect.}
  ## Checks whether values within the *same enum* have the same underlying value.
  ##
  ## .. code-block:: Nim
  ##  type
  ##    Enum1 = enum
  ##      Field1 = 3, Field2
  ##    Enum2 = enum
  ##      Place1, Place2 = 3
  ##  var
  ##    e1 = Field1
  ##    e2 = Enum1(Place2)
  ##  echo (e1 == e2) # true
  ##  echo (e1 == Place2) # raises error
proc `==`*(x, y: pointer): bool {.magic: "EqRef", noSideEffect.}
  ## .. code-block:: Nim
  ##  var # this is a wildly dangerous example
  ##    a = cast[pointer](0)
  ##    b = cast[pointer](nil)
  ##  echo (a == b) # true due to the special meaning of `nil`/0 as a pointer
proc `==`*(x, y: string): bool {.magic: "EqStr", noSideEffect.}
  ## Checks for equality between two `string` variables.

proc `==`*(x, y: char): bool {.magic: "EqCh", noSideEffect.}
  ## Checks for equality between two `char` variables.
proc `==`*(x, y: bool): bool {.magic: "EqB", noSideEffect.}
  ## Checks for equality between two `bool` variables.
proc `==`*[T](x, y: set[T]): bool {.magic: "EqSet", noSideEffect.}
  ## Checks for equality between two variables of type `set`.
  ##
  ## .. code-block:: Nim
  ##  var a = {1, 2, 2, 3} # duplication in sets is ignored
  ##  var b = {1, 2, 3}
  ##  echo (a == b) # true
proc `==`*[T](x, y: ref T): bool {.magic: "EqRef", noSideEffect.}
  ## Checks that two `ref` variables refer to the same item.
proc `==`*[T](x, y: ptr T): bool {.magic: "EqRef", noSideEffect.}
  ## Checks that two `ptr` variables refer to the same item.
proc `==`*[T: proc](x, y: T): bool {.magic: "EqProc", noSideEffect.}
  ## Checks that two `proc` variables refer to the same procedure.

proc `<=`*[Enum: enum](x, y: Enum): bool {.magic: "LeEnum", noSideEffect.}
proc `<=`*(x, y: string): bool {.magic: "LeStr", noSideEffect.}
  ## Compares two strings and returns true if `x` is lexicographically
  ## before `y` (uppercase letters come before lowercase letters).
  ##
  ## .. code-block:: Nim
  ##     let
  ##       a = "abc"
  ##       b = "abd"
  ##       c = "ZZZ"
  ##     assert a <= b
  ##     assert a <= a
  ##     assert (a <= c) == false
proc `<=`*(x, y: char): bool {.magic: "LeCh", noSideEffect.}
  ## Compares two chars and returns true if `x` is lexicographically
  ## before `y` (uppercase letters come before lowercase letters).
  ##
  ## .. code-block:: Nim
  ##     let
  ##       a = 'a'
  ##       b = 'b'
  ##       c = 'Z'
  ##     assert a <= b
  ##     assert a <= a
  ##     assert (a <= c) == false
proc `<=`*[T](x, y: set[T]): bool {.magic: "LeSet", noSideEffect.}
  ## Returns true if `x` is a subset of `y`.
  ##
  ## A subset `x` has all of its members in `y` and `y` doesn't necessarily
  ## have more members than `x`. That is, `x` can be equal to `y`.
  ##
  ## .. code-block:: Nim
  ##   let
  ##     a = {3, 5}
  ##     b = {1, 3, 5, 7}
  ##     c = {2}
  ##   assert a <= b
  ##   assert a <= a
  ##   assert (a <= c) == false
proc `<=`*(x, y: bool): bool {.magic: "LeB", noSideEffect.}
proc `<=`*[T](x, y: ref T): bool {.magic: "LePtr", noSideEffect.}
proc `<=`*(x, y: pointer): bool {.magic: "LePtr", noSideEffect.}

proc `<`*[Enum: enum](x, y: Enum): bool {.magic: "LtEnum", noSideEffect.}
proc `<`*(x, y: string): bool {.magic: "LtStr", noSideEffect.}
  ## Compares two strings and returns true if `x` is lexicographically
  ## before `y` (uppercase letters come before lowercase letters).
  ##
  ## .. code-block:: Nim
  ##     let
  ##       a = "abc"
  ##       b = "abd"
  ##       c = "ZZZ"
  ##     assert a < b
  ##     assert (a < a) == false
  ##     assert (a < c) == false
proc `<`*(x, y: char): bool {.magic: "LtCh", noSideEffect.}
  ## Compares two chars and returns true if `x` is lexicographically
  ## before `y` (uppercase letters come before lowercase letters).
  ##
  ## .. code-block:: Nim
  ##     let
  ##       a = 'a'
  ##       b = 'b'
  ##       c = 'Z'
  ##     assert a < b
  ##     assert (a < a) == false
  ##     assert (a < c) == false
proc `<`*[T](x, y: set[T]): bool {.magic: "LtSet", noSideEffect.}
  ## Returns true if `x` is a strict or proper subset of `y`.
  ##
  ## A strict or proper subset `x` has all of its members in `y` but `y` has
  ## more elements than `y`.
  ##
  ## .. code-block:: Nim
  ##   let
  ##     a = {3, 5}
  ##     b = {1, 3, 5, 7}
  ##     c = {2}
  ##   assert a < b
  ##   assert (a < a) == false
  ##   assert (a < c) == false
proc `<`*(x, y: bool): bool {.magic: "LtB", noSideEffect.}
proc `<`*[T](x, y: ref T): bool {.magic: "LtPtr", noSideEffect.}
proc `<`*[T](x, y: ptr T): bool {.magic: "LtPtr", noSideEffect.}
proc `<`*(x, y: pointer): bool {.magic: "LtPtr", noSideEffect.}

template `!=`*(x, y: untyped): untyped =
  ## Unequals operator. This is a shorthand for ``not (x == y)``.
  not (x == y)

template `>=`*(x, y: untyped): untyped =
  ## "is greater or equals" operator. This is the same as ``y <= x``.
  y <= x

template `>`*(x, y: untyped): untyped =
  ## "is greater" operator. This is the same as ``y < x``.
  y < x

const
  appType* {.magic: "AppType"}: string = ""
    ## A string that describes the application type. Possible values:
    ## `"console"`, `"gui"`, `"lib"`.

include "system/inclrtl"

const NoFakeVars* = defined(nimscript) ## `true` if the backend doesn't support \
  ## "fake variables" like `var EBADF {.importc.}: cint`.

when not defined(JS) and not defined(nimSeqsV2):
  type
    TGenericSeq {.compilerproc, pure, inheritable.} = object
      len, reserved: int
      when defined(gogc):
        elemSize: int
    PGenericSeq {.exportc.} = ptr TGenericSeq
    # len and space without counting the terminating zero:
    NimStringDesc {.compilerproc, final.} = object of TGenericSeq
      data: UncheckedArray[char]
    NimString = ptr NimStringDesc

when not defined(JS) and not defined(nimscript):
  when not defined(nimSeqsV2):
    template space(s: PGenericSeq): int {.dirty.} =
      s.reserved and not (seqShallowFlag or strlitFlag)
  when not defined(nimV2):
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

  RootEffect* {.compilerproc.} = object of RootObj ## \
    ## Base effect class.
    ##
    ## Each effect should inherit from `RootEffect` unless you know what
    ## you're doing.
  TimeEffect* = object of RootEffect   ## Time effect.
  IOEffect* = object of RootEffect     ## IO effect.
  ReadIOEffect* = object of IOEffect   ## Effect describing a read IO operation.
  WriteIOEffect* = object of IOEffect  ## Effect describing a write IO operation.
  ExecIOEffect* = object of IOEffect   ## Effect describing an executing IO operation.

  StackTraceEntry* = object ## In debug mode exceptions store the stack trace that led
                            ## to them. A `StackTraceEntry` is a single entry of the
                            ## stack trace.
    procname*: cstring      ## Name of the proc that is currently executing.
    line*: int              ## Line number of the proc that is currently executing.
    filename*: cstring      ## Filename of the proc that is currently executing.

  Exception* {.compilerproc, magic: "Exception".} = object of RootObj ## \
    ## Base exception class.
    ##
    ## Each exception has to inherit from `Exception`. See the full `exception
    ## hierarchy <manual.html#exception-handling-exception-hierarchy>`_.
    parent*: ref Exception ## Parent exception (can be used as a stack).
    name*: cstring         ## The exception's name is its Nim identifier.
                           ## This field is filled automatically in the
                           ## ``raise`` statement.
    msg* {.exportc: "message".}: string ## The exception's message. Not
                                        ## providing an exception message
                                        ## is bad style.
    when defined(js):
      trace: string
    else:
      trace: seq[StackTraceEntry]
    when defined(nimBoostrapCsources0_19_0):
      # see #10315, bootstrap with `nim cpp` from csources gave error:
      # error: no member named 'raise_id' in 'Exception'
      raise_id: uint # set when exception is raised
    else:
      raiseId: uint # set when exception is raised
    up: ref Exception # used for stacking exceptions. Not exported!

  Defect* = object of Exception ## \
    ## Abstract base class for all exceptions that Nim's runtime raises
    ## but that are strictly uncatchable as they can also be mapped to
    ## a ``quit`` / ``trap`` / ``exit`` operation.

  CatchableError* = object of Exception ## \
    ## Abstract class for all exceptions that are catchable.
  IOError* = object of CatchableError ## \
    ## Raised if an IO error occurred.
  EOFError* = object of IOError ## \
    ## Raised if an IO "end of file" error occurred.
  OSError* = object of CatchableError ## \
    ## Raised if an operating system service failed.
    errorCode*: int32 ## OS-defined error code describing this error.
  LibraryError* = object of OSError ## \
    ## Raised if a dynamic library could not be loaded.
  ResourceExhaustedError* = object of CatchableError ## \
    ## Raised if a resource request could not be fulfilled.
  ArithmeticError* = object of Defect ## \
    ## Raised if any kind of arithmetic error occurred.
  DivByZeroError* = object of ArithmeticError ## \
    ## Raised for runtime integer divide-by-zero errors.

  OverflowError* = object of ArithmeticError ## \
    ## Raised for runtime integer overflows.
    ##
    ## This happens for calculations whose results are too large to fit in the
    ## provided bits.
  AccessViolationError* = object of Defect ## \
    ## Raised for invalid memory access errors
  AssertionError* = object of Defect ## \
    ## Raised when assertion is proved wrong.
    ##
    ## Usually the result of using the `assert() template
    ## <assertions.html#assert.t,untyped,string>`_.
  ValueError* = object of CatchableError ## \
    ## Raised for string and object conversion errors.
  KeyError* = object of ValueError ## \
    ## Raised if a key cannot be found in a table.
    ##
    ## Mostly used by the `tables <tables.html>`_ module, it can also be raised
    ## by other collection modules like `sets <sets.html>`_ or `strtabs
    ## <strtabs.html>`_.
  OutOfMemError* = object of Defect ## \
    ## Raised for unsuccessful attempts to allocate memory.
  IndexError* = object of Defect ## \
    ## Raised if an array index is out of bounds.

  FieldError* = object of Defect ## \
    ## Raised if a record field is not accessible because its discriminant's
    ## value does not fit.
  RangeError* = object of Defect ## \
    ## Raised if a range check error occurred.
  StackOverflowError* = object of Defect ## \
    ## Raised if the hardware stack used for subroutine calls overflowed.
  ReraiseError* = object of Defect ## \
    ## Raised if there is no exception to reraise.
  ObjectAssignmentError* = object of Defect ## \
    ## Raised if an object gets assigned to its parent's object.
  ObjectConversionError* = object of Defect ## \
    ## Raised if an object is converted to an incompatible object type.
    ## You can use ``of`` operator to check if conversion will succeed.
  FloatingPointError* = object of Defect ## \
    ## Base class for floating point exceptions.
  FloatInvalidOpError* = object of FloatingPointError ## \
    ## Raised by invalid operations according to IEEE.
    ##
    ## Raised by ``0.0/0.0``, for example.
  FloatDivByZeroError* = object of FloatingPointError ## \
    ## Raised by division by zero.
    ##
    ## Divisor is zero and dividend is a finite nonzero number.
  FloatOverflowError* = object of FloatingPointError ## \
    ## Raised for overflows.
    ##
    ## The operation produced a result that exceeds the range of the exponent.
  FloatUnderflowError* = object of FloatingPointError ## \
    ## Raised for underflows.
    ##
    ## The operation produced a result that is too small to be represented as a
    ## normal number.
  FloatInexactError* = object of FloatingPointError ## \
    ## Raised for inexact results.
    ##
    ## The operation produced a result that cannot be represented with infinite
    ## precision -- for example: ``2.0 / 3.0, log(1.1)``
    ##
    ## **Note**: Nim currently does not detect these!
  DeadThreadError* = object of Defect ## \
    ## Raised if it is attempted to send a message to a dead thread.
  NilAccessError* = object of Defect ## \
    ## Raised on dereferences of ``nil`` pointers.
    ##
    ## This is only raised if the `segfaults module <segfaults.html>`_ was imported!

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


proc succ*[T: Ordinal](x: T, y = 1): T {.magic: "Succ", noSideEffect.}
  ## Returns the ``y``-th successor (default: 1) of the value ``x``.
  ## ``T`` has to be an `ordinal type <#Ordinal>`_.
  ##
  ## If such a value does not exist, ``OverflowError`` is raised
  ## or a compile time error occurs.
  ##
  ## .. code-block:: Nim
  ##   let x = 5
  ##   echo succ(5)    # => 6
  ##   echo succ(5, 3) # => 8

proc pred*[T: Ordinal](x: T, y = 1): T {.magic: "Pred", noSideEffect.}
  ## Returns the ``y``-th predecessor (default: 1) of the value ``x``.
  ## ``T`` has to be an `ordinal type <#Ordinal>`_.
  ##
  ## If such a value does not exist, ``OverflowError`` is raised
  ## or a compile time error occurs.
  ##
  ## .. code-block:: Nim
  ##   let x = 5
  ##   echo pred(5)    # => 4
  ##   echo pred(5, 3) # => 2

proc inc*[T: Ordinal|uint|uint64](x: var T, y = 1) {.magic: "Inc", noSideEffect.}
  ## Increments the ordinal ``x`` by ``y``.
  ##
  ## If such a value does not exist, ``OverflowError`` is raised or a compile
  ## time error occurs. This is a short notation for: ``x = succ(x, y)``.
  ##
  ## .. code-block:: Nim
  ##  var i = 2
  ##  inc(i)    # i <- 3
  ##  inc(i, 3) # i <- 6

proc dec*[T: Ordinal|uint|uint64](x: var T, y = 1) {.magic: "Dec", noSideEffect.}
  ## Decrements the ordinal ``x`` by ``y``.
  ##
  ## If such a value does not exist, ``OverflowError`` is raised or a compile
  ## time error occurs. This is a short notation for: ``x = pred(x, y)``.
  ##
  ## .. code-block:: Nim
  ##  var i = 2
  ##  dec(i)    # i <- 1
  ##  dec(i, 3) # i <- -2

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

when not defined(JS):
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

# set routines:
proc incl*[T](x: var set[T], y: T) {.magic: "Incl", noSideEffect.}
  ## Includes element ``y`` in the set ``x``.
  ##
  ## This is the same as ``x = x + {y}``, but it might be more efficient.
  ##
  ## .. code-block:: Nim
  ##   var a = {1, 3, 5}
  ##   a.incl(2) # a <- {1, 2, 3, 5}
  ##   a.incl(4) # a <- {1, 2, 3, 4, 5}

template incl*[T](x: var set[T], y: set[T]) =
  ## Includes the set ``y`` in the set ``x``.
  ##
  ## .. code-block:: Nim
  ##   var a = {1, 3, 5, 7}
  ##   var b = {4, 5, 6}
  ##   a.incl(b)  # a <- {1, 3, 4, 5, 6, 7}
  x = x + y

proc excl*[T](x: var set[T], y: T) {.magic: "Excl", noSideEffect.}
  ## Excludes element ``y`` from the set ``x``.
  ##
  ## This is the same as ``x = x - {y}``, but it might be more efficient.
  ##
  ## .. code-block:: Nim
  ##   var b = {2, 3, 5, 6, 12, 545}
  ##   b.excl(5)  # b <- {2, 3, 6, 12, 545}

template excl*[T](x: var set[T], y: set[T]) =
  ## Excludes the set ``y`` from the set ``x``.
  ##
  ## .. code-block:: Nim
  ##   var a = {1, 3, 5, 7}
  ##   var b = {3, 4, 5}
  ##   a.excl(b)  # a <- {1, 7}
  x = x - y

proc card*[T](x: set[T]): int {.magic: "Card", noSideEffect.}
  ## Returns the cardinality of the set ``x``, i.e. the number of elements
  ## in the set.
  ##
  ## .. code-block:: Nim
  ##   var a = {1, 3, 5, 7}
  ##   echo card(a) # => 4

proc len*[T](x: set[T]): int {.magic: "Card", noSideEffect.}
  ## An alias for `card(x)`.

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

# --------------------------------------------------------------------------
# built-in operators

when defined(nimNoZeroExtendMagic):
  proc ze*(x: int8): int {.deprecated.} =
    ## zero extends a smaller integer type to ``int``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

    cast[int](uint(cast[uint8](x)))

  proc ze*(x: int16): int {.deprecated.} =
    ## zero extends a smaller integer type to ``int``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.
    cast[int](uint(cast[uint16](x)))

  proc ze64*(x: int8): int64 {.deprecated.} =
    ## zero extends a smaller integer type to ``int64``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.
    cast[int64](uint64(cast[uint8](x)))

  proc ze64*(x: int16): int64 {.deprecated.} =
    ## zero extends a smaller integer type to ``int64``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.
    cast[int64](uint64(cast[uint16](x)))

  proc ze64*(x: int32): int64 {.deprecated.} =
    ## zero extends a smaller integer type to ``int64``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.
    cast[int64](uint64(cast[uint32](x)))

  proc ze64*(x: int): int64 {.deprecated.} =
    ## zero extends a smaller integer type to ``int64``. This treats `x` as
    ## unsigned. Does nothing if the size of an ``int`` is the same as ``int64``.
    ## (This is the case on 64 bit processors.)
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.
    cast[int64](uint64(cast[uint](x)))

  proc toU8*(x: int): int8 {.deprecated.} =
    ## treats `x` as unsigned and converts it to a byte by taking the last 8 bits
    ## from `x`.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.
    cast[int8](x)

  proc toU16*(x: int): int16 {.deprecated.} =
    ## treats `x` as unsigned and converts it to an ``int16`` by taking the last
    ## 16 bits from `x`.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.
    cast[int16](x)

  proc toU32*(x: int64): int32 {.deprecated.} =
    ## treats `x` as unsigned and converts it to an ``int32`` by taking the
    ## last 32 bits from `x`.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.
    cast[int32](x)

elif not defined(JS):
  proc ze*(x: int8): int {.magic: "Ze8ToI", noSideEffect, deprecated.}
    ## zero extends a smaller integer type to ``int``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

  proc ze*(x: int16): int {.magic: "Ze16ToI", noSideEffect, deprecated.}
    ## zero extends a smaller integer type to ``int``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

  proc ze64*(x: int8): int64 {.magic: "Ze8ToI64", noSideEffect, deprecated.}
    ## zero extends a smaller integer type to ``int64``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

  proc ze64*(x: int16): int64 {.magic: "Ze16ToI64", noSideEffect, deprecated.}
    ## zero extends a smaller integer type to ``int64``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

  proc ze64*(x: int32): int64 {.magic: "Ze32ToI64", noSideEffect, deprecated.}
    ## zero extends a smaller integer type to ``int64``. This treats `x` as
    ## unsigned.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

  proc ze64*(x: int): int64 {.magic: "ZeIToI64", noSideEffect, deprecated.}
    ## zero extends a smaller integer type to ``int64``. This treats `x` as
    ## unsigned. Does nothing if the size of an ``int`` is the same as ``int64``.
    ## (This is the case on 64 bit processors.)
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

  proc toU8*(x: int): int8 {.magic: "ToU8", noSideEffect, deprecated.}
    ## treats `x` as unsigned and converts it to a byte by taking the last 8 bits
    ## from `x`.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

  proc toU16*(x: int): int16 {.magic: "ToU16", noSideEffect, deprecated.}
    ## treats `x` as unsigned and converts it to an ``int16`` by taking the last
    ## 16 bits from `x`.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

  proc toU32*(x: int64): int32 {.magic: "ToU32", noSideEffect, deprecated.}
    ## treats `x` as unsigned and converts it to an ``int32`` by taking the
    ## last 32 bits from `x`.
    ## **Deprecated since version 0.19.9**: Use unsigned integers instead.

# integer calculations:
proc `+`*(x: int): int {.magic: "UnaryPlusI", noSideEffect.}
  ## Unary `+` operator for an integer. Has no effect.
proc `+`*(x: int8): int8 {.magic: "UnaryPlusI", noSideEffect.}
proc `+`*(x: int16): int16 {.magic: "UnaryPlusI", noSideEffect.}
proc `+`*(x: int32): int32 {.magic: "UnaryPlusI", noSideEffect.}
proc `+`*(x: int64): int64 {.magic: "UnaryPlusI", noSideEffect.}

proc `-`*(x: int): int {.magic: "UnaryMinusI", noSideEffect.}
  ## Unary `-` operator for an integer. Negates `x`.
proc `-`*(x: int8): int8 {.magic: "UnaryMinusI", noSideEffect.}
proc `-`*(x: int16): int16 {.magic: "UnaryMinusI", noSideEffect.}
proc `-`*(x: int32): int32 {.magic: "UnaryMinusI", noSideEffect.}
proc `-`*(x: int64): int64 {.magic: "UnaryMinusI64", noSideEffect.}

proc `not`*(x: int): int {.magic: "BitnotI", noSideEffect.}
  ## Computes the `bitwise complement` of the integer `x`.
  ##
  ## .. code-block:: Nim
  ##   var
  ##     a = 0'u8
  ##     b = 0'i8
  ##     c = 1000'u16
  ##     d = 1000'i16
  ##
  ##   echo not a # => 255
  ##   echo not b # => -1
  ##   echo not c # => 64535
  ##   echo not d # => -1001
proc `not`*(x: int8): int8 {.magic: "BitnotI", noSideEffect.}
proc `not`*(x: int16): int16 {.magic: "BitnotI", noSideEffect.}
proc `not`*(x: int32): int32 {.magic: "BitnotI", noSideEffect.}
proc `not`*(x: int64): int64 {.magic: "BitnotI", noSideEffect.}

proc `+`*(x, y: int): int {.magic: "AddI", noSideEffect.}
  ## Binary `+` operator for an integer.
proc `+`*(x, y: int8): int8 {.magic: "AddI", noSideEffect.}
proc `+`*(x, y: int16): int16 {.magic: "AddI", noSideEffect.}
proc `+`*(x, y: int32): int32 {.magic: "AddI", noSideEffect.}
proc `+`*(x, y: int64): int64 {.magic: "AddI", noSideEffect.}

proc `-`*(x, y: int): int {.magic: "SubI", noSideEffect.}
  ## Binary `-` operator for an integer.
proc `-`*(x, y: int8): int8 {.magic: "SubI", noSideEffect.}
proc `-`*(x, y: int16): int16 {.magic: "SubI", noSideEffect.}
proc `-`*(x, y: int32): int32 {.magic: "SubI", noSideEffect.}
proc `-`*(x, y: int64): int64 {.magic: "SubI", noSideEffect.}

proc `*`*(x, y: int): int {.magic: "MulI", noSideEffect.}
  ## Binary `*` operator for an integer.
proc `*`*(x, y: int8): int8 {.magic: "MulI", noSideEffect.}
proc `*`*(x, y: int16): int16 {.magic: "MulI", noSideEffect.}
proc `*`*(x, y: int32): int32 {.magic: "MulI", noSideEffect.}
proc `*`*(x, y: int64): int64 {.magic: "MulI", noSideEffect.}

proc `div`*(x, y: int): int {.magic: "DivI", noSideEffect.}
  ## Computes the integer division.
  ##
  ## This is roughly the same as ``trunc(x/y)``.
  ##
  ## .. code-block:: Nim
  ##   ( 1 div  2) ==  0
  ##   ( 2 div  2) ==  1
  ##   ( 3 div  2) ==  1
  ##   ( 7 div  3) ==  2
  ##   (-7 div  3) == -2
  ##   ( 7 div -3) == -2
  ##   (-7 div -3) ==  2
proc `div`*(x, y: int8): int8 {.magic: "DivI", noSideEffect.}
proc `div`*(x, y: int16): int16 {.magic: "DivI", noSideEffect.}
proc `div`*(x, y: int32): int32 {.magic: "DivI", noSideEffect.}
proc `div`*(x, y: int64): int64 {.magic: "DivI", noSideEffect.}

proc `mod`*(x, y: int): int {.magic: "ModI", noSideEffect.}
  ## Computes the integer modulo operation (remainder).
  ##
  ## This is the same as ``x - (x div y) * y``.
  ##
  ## .. code-block:: Nim
  ##   ( 7 mod  5) ==  2
  ##   (-7 mod  5) == -2
  ##   ( 7 mod -5) ==  2
  ##   (-7 mod -5) == -2
proc `mod`*(x, y: int8): int8 {.magic: "ModI", noSideEffect.}
proc `mod`*(x, y: int16): int16 {.magic: "ModI", noSideEffect.}
proc `mod`*(x, y: int32): int32 {.magic: "ModI", noSideEffect.}
proc `mod`*(x, y: int64): int64 {.magic: "ModI", noSideEffect.}

when defined(nimOldShiftRight) or not defined(nimAshr):
  const shrDepMessage = "`shr` will become sign preserving."
  proc `shr`*(x: int, y: SomeInteger): int {.magic: "ShrI", noSideEffect, deprecated: shrDepMessage.}
  proc `shr`*(x: int8, y: SomeInteger): int8 {.magic: "ShrI", noSideEffect, deprecated: shrDepMessage.}
  proc `shr`*(x: int16, y: SomeInteger): int16 {.magic: "ShrI", noSideEffect, deprecated: shrDepMessage.}
  proc `shr`*(x: int32, y: SomeInteger): int32 {.magic: "ShrI", noSideEffect, deprecated: shrDepMessage.}
  proc `shr`*(x: int64, y: SomeInteger): int64 {.magic: "ShrI", noSideEffect, deprecated: shrDepMessage.}
else:
  proc `shr`*(x: int, y: SomeInteger): int {.magic: "AshrI", noSideEffect.}
    ## Computes the `shift right` operation of `x` and `y`, filling
    ## vacant bit positions with the sign bit.
    ##
    ## **Note**: `Operator precedence <manual.html#syntax-precedence>`_
    ## is different than in *C*.
    ##
    ## See also:
    ## * `ashr proc <#ashr,int,SomeInteger>`_ for arithmetic shift right
    ##
    ## .. code-block:: Nim
    ##   0b0001_0000'i8 shr 2 == 0b0000_0100'i8
    ##   0b0000_0001'i8 shr 1 == 0b0000_0000'i8
    ##   0b1000_0000'i8 shr 4 == 0b1111_1000'i8
    ##   -1 shr 5 == -1
    ##   1 shr 5 == 0
    ##   16 shr 2 == 4
    ##   -16 shr 2 == -4
  proc `shr`*(x: int8, y: SomeInteger): int8 {.magic: "AshrI", noSideEffect.}
  proc `shr`*(x: int16, y: SomeInteger): int16 {.magic: "AshrI", noSideEffect.}
  proc `shr`*(x: int32, y: SomeInteger): int32 {.magic: "AshrI", noSideEffect.}
  proc `shr`*(x: int64, y: SomeInteger): int64 {.magic: "AshrI", noSideEffect.}


proc `shl`*(x: int, y: SomeInteger): int {.magic: "ShlI", noSideEffect.}
  ## Computes the `shift left` operation of `x` and `y`.
  ##
  ## **Note**: `Operator precedence <manual.html#syntax-precedence>`_
  ## is different than in *C*.
  ##
  ## .. code-block:: Nim
  ##  1'i32 shl 4 == 0x0000_0010
  ##  1'i64 shl 4 == 0x0000_0000_0000_0010
proc `shl`*(x: int8, y: SomeInteger): int8 {.magic: "ShlI", noSideEffect.}
proc `shl`*(x: int16, y: SomeInteger): int16 {.magic: "ShlI", noSideEffect.}
proc `shl`*(x: int32, y: SomeInteger): int32 {.magic: "ShlI", noSideEffect.}
proc `shl`*(x: int64, y: SomeInteger): int64 {.magic: "ShlI", noSideEffect.}

when defined(nimAshr):
  proc ashr*(x: int, y: SomeInteger): int {.magic: "AshrI", noSideEffect.}
    ## Shifts right by pushing copies of the leftmost bit in from the left,
    ## and let the rightmost bits fall off.
    ##
    ## Note that `ashr` is not an operator so use the normal function
    ## call syntax for it.
    ##
    ## See also:
    ## * `shr proc <#shr,int,SomeInteger>`_
    ##
    ## .. code-block:: Nim
    ##   ashr(0b0001_0000'i8, 2) == 0b0000_0100'i8
    ##   ashr(0b1000_0000'i8, 8) == 0b1111_1111'i8
    ##   ashr(0b1000_0000'i8, 1) == 0b1100_0000'i8
  proc ashr*(x: int8, y: SomeInteger): int8 {.magic: "AshrI", noSideEffect.}
  proc ashr*(x: int16, y: SomeInteger): int16 {.magic: "AshrI", noSideEffect.}
  proc ashr*(x: int32, y: SomeInteger): int32 {.magic: "AshrI", noSideEffect.}
  proc ashr*(x: int64, y: SomeInteger): int64 {.magic: "AshrI", noSideEffect.}
else:
  # used for bootstrapping the compiler
  proc ashr*[T](x: T, y: SomeInteger): T = discard

proc `and`*(x, y: int): int {.magic: "BitandI", noSideEffect.}
  ## Computes the `bitwise and` of numbers `x` and `y`.
  ##
  ## .. code-block:: Nim
  ##   (0b0011 and 0b0101) == 0b0001
  ##   (0b0111 and 0b1100) == 0b0100
proc `and`*(x, y: int8): int8 {.magic: "BitandI", noSideEffect.}
proc `and`*(x, y: int16): int16 {.magic: "BitandI", noSideEffect.}
proc `and`*(x, y: int32): int32 {.magic: "BitandI", noSideEffect.}
proc `and`*(x, y: int64): int64 {.magic: "BitandI", noSideEffect.}

proc `or`*(x, y: int): int {.magic: "BitorI", noSideEffect.}
  ## Computes the `bitwise or` of numbers `x` and `y`.
  ##
  ## .. code-block:: Nim
  ##   (0b0011 or 0b0101) == 0b0111
  ##   (0b0111 or 0b1100) == 0b1111
proc `or`*(x, y: int8): int8 {.magic: "BitorI", noSideEffect.}
proc `or`*(x, y: int16): int16 {.magic: "BitorI", noSideEffect.}
proc `or`*(x, y: int32): int32 {.magic: "BitorI", noSideEffect.}
proc `or`*(x, y: int64): int64 {.magic: "BitorI", noSideEffect.}

proc `xor`*(x, y: int): int {.magic: "BitxorI", noSideEffect.}
  ## Computes the `bitwise xor` of numbers `x` and `y`.
  ##
  ## .. code-block:: Nim
  ##   (0b0011 xor 0b0101) == 0b0110
  ##   (0b0111 xor 0b1100) == 0b1011
proc `xor`*(x, y: int8): int8 {.magic: "BitxorI", noSideEffect.}
proc `xor`*(x, y: int16): int16 {.magic: "BitxorI", noSideEffect.}
proc `xor`*(x, y: int32): int32 {.magic: "BitxorI", noSideEffect.}
proc `xor`*(x, y: int64): int64 {.magic: "BitxorI", noSideEffect.}

proc `==`*(x, y: int): bool {.magic: "EqI", noSideEffect.}
  ## Compares two integers for equality.
proc `==`*(x, y: int8): bool {.magic: "EqI", noSideEffect.}
proc `==`*(x, y: int16): bool {.magic: "EqI", noSideEffect.}
proc `==`*(x, y: int32): bool {.magic: "EqI", noSideEffect.}
proc `==`*(x, y: int64): bool {.magic: "EqI", noSideEffect.}

proc `<=`*(x, y: int): bool {.magic: "LeI", noSideEffect.}
  ## Returns true if `x` is less than or equal to `y`.
proc `<=`*(x, y: int8): bool {.magic: "LeI", noSideEffect.}
proc `<=`*(x, y: int16): bool {.magic: "LeI", noSideEffect.}
proc `<=`*(x, y: int32): bool {.magic: "LeI", noSideEffect.}
proc `<=`*(x, y: int64): bool {.magic: "LeI", noSideEffect.}

proc `<`*(x, y: int): bool {.magic: "LtI", noSideEffect.}
  ## Returns true if `x` is less than `y`.
proc `<`*(x, y: int8): bool {.magic: "LtI", noSideEffect.}
proc `<`*(x, y: int16): bool {.magic: "LtI", noSideEffect.}
proc `<`*(x, y: int32): bool {.magic: "LtI", noSideEffect.}
proc `<`*(x, y: int64): bool {.magic: "LtI", noSideEffect.}

type
  IntMax32 = int|int8|int16|int32

proc `+%`*(x, y: IntMax32): IntMax32 {.magic: "AddU", noSideEffect.}
proc `+%`*(x, y: int64): int64 {.magic: "AddU", noSideEffect.}
  ## Treats `x` and `y` as unsigned and adds them.
  ##
  ## The result is truncated to fit into the result.
  ## This implements modulo arithmetic. No overflow errors are possible.

proc `-%`*(x, y: IntMax32): IntMax32 {.magic: "SubU", noSideEffect.}
proc `-%`*(x, y: int64): int64 {.magic: "SubU", noSideEffect.}
  ## Treats `x` and `y` as unsigned and subtracts them.
  ##
  ## The result is truncated to fit into the result.
  ## This implements modulo arithmetic. No overflow errors are possible.

proc `*%`*(x, y: IntMax32): IntMax32 {.magic: "MulU", noSideEffect.}
proc `*%`*(x, y: int64): int64 {.magic: "MulU", noSideEffect.}
  ## Treats `x` and `y` as unsigned and multiplies them.
  ##
  ## The result is truncated to fit into the result.
  ## This implements modulo arithmetic. No overflow errors are possible.

proc `/%`*(x, y: IntMax32): IntMax32 {.magic: "DivU", noSideEffect.}
proc `/%`*(x, y: int64): int64 {.magic: "DivU", noSideEffect.}
  ## Treats `x` and `y` as unsigned and divides them.
  ##
  ## The result is truncated to fit into the result.
  ## This implements modulo arithmetic. No overflow errors are possible.

proc `%%`*(x, y: IntMax32): IntMax32 {.magic: "ModU", noSideEffect.}
proc `%%`*(x, y: int64): int64 {.magic: "ModU", noSideEffect.}
  ## Treats `x` and `y` as unsigned and compute the modulo of `x` and `y`.
  ##
  ## The result is truncated to fit into the result.
  ## This implements modulo arithmetic. No overflow errors are possible.

proc `<=%`*(x, y: IntMax32): bool {.magic: "LeU", noSideEffect.}
proc `<=%`*(x, y: int64): bool {.magic: "LeU64", noSideEffect.}
  ## Treats `x` and `y` as unsigned and compares them.
  ## Returns true if ``unsigned(x) <= unsigned(y)``.

proc `<%`*(x, y: IntMax32): bool {.magic: "LtU", noSideEffect.}
proc `<%`*(x, y: int64): bool {.magic: "LtU64", noSideEffect.}
  ## Treats `x` and `y` as unsigned and compares them.
  ## Returns true if ``unsigned(x) < unsigned(y)``.

template `>=%`*(x, y: untyped): untyped = y <=% x
  ## Treats `x` and `y` as unsigned and compares them.
  ## Returns true if ``unsigned(x) >= unsigned(y)``.

template `>%`*(x, y: untyped): untyped = y <% x
  ## Treats `x` and `y` as unsigned and compares them.
  ## Returns true if ``unsigned(x) > unsigned(y)``.


# unsigned integer operations:
proc `not`*(x: uint): uint {.magic: "BitnotI", noSideEffect.}
  ## Computes the `bitwise complement` of the integer `x`.
proc `not`*(x: uint8): uint8 {.magic: "BitnotI", noSideEffect.}
proc `not`*(x: uint16): uint16 {.magic: "BitnotI", noSideEffect.}
proc `not`*(x: uint32): uint32 {.magic: "BitnotI", noSideEffect.}
proc `not`*(x: uint64): uint64 {.magic: "BitnotI", noSideEffect.}

proc `shr`*(x: uint, y: SomeInteger): uint {.magic: "ShrI", noSideEffect.}
  ## Computes the `shift right` operation of `x` and `y`.
proc `shr`*(x: uint8, y: SomeInteger): uint8 {.magic: "ShrI", noSideEffect.}
proc `shr`*(x: uint16, y: SomeInteger): uint16 {.magic: "ShrI", noSideEffect.}
proc `shr`*(x: uint32, y: SomeInteger): uint32 {.magic: "ShrI", noSideEffect.}
proc `shr`*(x: uint64, y: SomeInteger): uint64 {.magic: "ShrI", noSideEffect.}

proc `shl`*(x: uint, y: SomeInteger): uint {.magic: "ShlI", noSideEffect.}
  ## Computes the `shift left` operation of `x` and `y`.
proc `shl`*(x: uint8, y: SomeInteger): uint8 {.magic: "ShlI", noSideEffect.}
proc `shl`*(x: uint16, y: SomeInteger): uint16 {.magic: "ShlI", noSideEffect.}
proc `shl`*(x: uint32, y: SomeInteger): uint32 {.magic: "ShlI", noSideEffect.}
proc `shl`*(x: uint64, y: SomeInteger): uint64 {.magic: "ShlI", noSideEffect.}

proc `and`*(x, y: uint): uint {.magic: "BitandI", noSideEffect.}
  ## Computes the `bitwise and` of numbers `x` and `y`.
proc `and`*(x, y: uint8): uint8 {.magic: "BitandI", noSideEffect.}
proc `and`*(x, y: uint16): uint16 {.magic: "BitandI", noSideEffect.}
proc `and`*(x, y: uint32): uint32 {.magic: "BitandI", noSideEffect.}
proc `and`*(x, y: uint64): uint64 {.magic: "BitandI", noSideEffect.}

proc `or`*(x, y: uint): uint {.magic: "BitorI", noSideEffect.}
  ## Computes the `bitwise or` of numbers `x` and `y`.
proc `or`*(x, y: uint8): uint8 {.magic: "BitorI", noSideEffect.}
proc `or`*(x, y: uint16): uint16 {.magic: "BitorI", noSideEffect.}
proc `or`*(x, y: uint32): uint32 {.magic: "BitorI", noSideEffect.}
proc `or`*(x, y: uint64): uint64 {.magic: "BitorI", noSideEffect.}

proc `xor`*(x, y: uint): uint {.magic: "BitxorI", noSideEffect.}
  ## Computes the `bitwise xor` of numbers `x` and `y`.
proc `xor`*(x, y: uint8): uint8 {.magic: "BitxorI", noSideEffect.}
proc `xor`*(x, y: uint16): uint16 {.magic: "BitxorI", noSideEffect.}
proc `xor`*(x, y: uint32): uint32 {.magic: "BitxorI", noSideEffect.}
proc `xor`*(x, y: uint64): uint64 {.magic: "BitxorI", noSideEffect.}

proc `==`*(x, y: uint): bool {.magic: "EqI", noSideEffect.}
  ## Compares two unsigned integers for equality.
proc `==`*(x, y: uint8): bool {.magic: "EqI", noSideEffect.}
proc `==`*(x, y: uint16): bool {.magic: "EqI", noSideEffect.}
proc `==`*(x, y: uint32): bool {.magic: "EqI", noSideEffect.}
proc `==`*(x, y: uint64): bool {.magic: "EqI", noSideEffect.}

proc `+`*(x, y: uint): uint {.magic: "AddU", noSideEffect.}
  ## Binary `+` operator for unsigned integers.
proc `+`*(x, y: uint8): uint8 {.magic: "AddU", noSideEffect.}
proc `+`*(x, y: uint16): uint16 {.magic: "AddU", noSideEffect.}
proc `+`*(x, y: uint32): uint32 {.magic: "AddU", noSideEffect.}
proc `+`*(x, y: uint64): uint64 {.magic: "AddU", noSideEffect.}

proc `-`*(x, y: uint): uint {.magic: "SubU", noSideEffect.}
  ## Binary `-` operator for unsigned integers.
proc `-`*(x, y: uint8): uint8 {.magic: "SubU", noSideEffect.}
proc `-`*(x, y: uint16): uint16 {.magic: "SubU", noSideEffect.}
proc `-`*(x, y: uint32): uint32 {.magic: "SubU", noSideEffect.}
proc `-`*(x, y: uint64): uint64 {.magic: "SubU", noSideEffect.}

proc `*`*(x, y: uint): uint {.magic: "MulU", noSideEffect.}
  ## Binary `*` operator for unsigned integers.
proc `*`*(x, y: uint8): uint8 {.magic: "MulU", noSideEffect.}
proc `*`*(x, y: uint16): uint16 {.magic: "MulU", noSideEffect.}
proc `*`*(x, y: uint32): uint32 {.magic: "MulU", noSideEffect.}
proc `*`*(x, y: uint64): uint64 {.magic: "MulU", noSideEffect.}

proc `div`*(x, y: uint): uint {.magic: "DivU", noSideEffect.}
  ## Computes the integer division for unsigned integers.
  ## This is roughly the same as ``trunc(x/y)``.
proc `div`*(x, y: uint8): uint8 {.magic: "DivU", noSideEffect.}
proc `div`*(x, y: uint16): uint16 {.magic: "DivU", noSideEffect.}
proc `div`*(x, y: uint32): uint32 {.magic: "DivU", noSideEffect.}
proc `div`*(x, y: uint64): uint64 {.magic: "DivU", noSideEffect.}

proc `mod`*(x, y: uint): uint {.magic: "ModU", noSideEffect.}
  ## Computes the integer modulo operation (remainder) for unsigned integers.
  ## This is the same as ``x - (x div y) * y``.
proc `mod`*(x, y: uint8): uint8 {.magic: "ModU", noSideEffect.}
proc `mod`*(x, y: uint16): uint16 {.magic: "ModU", noSideEffect.}
proc `mod`*(x, y: uint32): uint32 {.magic: "ModU", noSideEffect.}
proc `mod`*(x, y: uint64): uint64 {.magic: "ModU", noSideEffect.}

proc `<=`*(x, y: uint): bool {.magic: "LeU", noSideEffect.}
  ## Returns true if ``x <= y``.
proc `<=`*(x, y: uint8): bool {.magic: "LeU", noSideEffect.}
proc `<=`*(x, y: uint16): bool {.magic: "LeU", noSideEffect.}
proc `<=`*(x, y: uint32): bool {.magic: "LeU", noSideEffect.}
proc `<=`*(x, y: uint64): bool {.magic: "LeU", noSideEffect.}

proc `<`*(x, y: uint): bool {.magic: "LtU", noSideEffect.}
  ## Returns true if ``unsigned(x) < unsigned(y)``.
proc `<`*(x, y: uint8): bool {.magic: "LtU", noSideEffect.}
proc `<`*(x, y: uint16): bool {.magic: "LtU", noSideEffect.}
proc `<`*(x, y: uint32): bool {.magic: "LtU", noSideEffect.}
proc `<`*(x, y: uint64): bool {.magic: "LtU", noSideEffect.}

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

# set operators
proc `*`*[T](x, y: set[T]): set[T] {.magic: "MulSet", noSideEffect.}
  ## This operator computes the intersection of two sets.
  ##
  ## .. code-block:: Nim
  ##   let
  ##     a = {1, 2, 3}
  ##     b = {2, 3, 4}
  ##   echo a * b # => {2, 3}
proc `+`*[T](x, y: set[T]): set[T] {.magic: "PlusSet", noSideEffect.}
  ## This operator computes the union of two sets.
  ##
  ## .. code-block:: Nim
  ##   let
  ##     a = {1, 2, 3}
  ##     b = {2, 3, 4}
  ##   echo a + b # => {1, 2, 3, 4}
proc `-`*[T](x, y: set[T]): set[T] {.magic: "MinusSet", noSideEffect.}
  ## This operator computes the difference of two sets.
  ##
  ## .. code-block:: Nim
  ##   let
  ##     a = {1, 2, 3}
  ##     b = {2, 3, 4}
  ##   echo a - b # => {1}

proc contains*[T](x: set[T], y: T): bool {.magic: "InSet", noSideEffect.}
  ## One should overload this proc if one wants to overload the ``in`` operator.
  ##
  ## The parameters are in reverse order! ``a in b`` is a template for
  ## ``contains(b, a)``.
  ## This is because the unification algorithm that Nim uses for overload
  ## resolution works from left to right.
  ## But for the ``in`` operator that would be the wrong direction for this
  ## piece of code:
  ##
  ## .. code-block:: Nim
  ##   var s: set[range['a'..'z']] = {'a'..'c'}
  ##   assert s.contains('c')
  ##   assert 'b' in s
  ##
  ## If ``in`` had been declared as ``[T](elem: T, s: set[T])`` then ``T`` would
  ## have been bound to ``char``. But ``s`` is not compatible to type
  ## ``set[char]``! The solution is to bind ``T`` to ``range['a'..'z']``. This
  ## is achieved by reversing the parameters for ``contains``; ``in`` then
  ## passes its arguments in reverse order.

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
  ##   assert(FloatingPointError of Exception)
  ##   assert(DivByZeroError of Exception)

proc cmp*[T](x, y: T): int {.procvar.} =
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
