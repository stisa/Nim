discard """
  output: "came here"
"""

#BUG
type
  TAnyKind = enum
    nkInt,
    nkFloat,
    nkString
  TAny = object
    case kind: TAnyKind
    of nkInt: intVal: int
    of nkFloat: floatVal: float
    of nkString: strVal: string

var s: TAny
s = TAny(kind: nkString, strVal: "test")

var nr: TAny
s = TAny(kind: nkInt, intVal: 78)


# s = nr # works
nr = s # fails!
echo "came here"
