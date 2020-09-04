
proc newObjType(n:PNode,res: var ESNode) =
  #[for:
    type A = object
      b: int
    we want something like:
    function A(b) {
      this.b = b;
      return this;
    }
    which in ast form is:
    "type": "FunctionDeclaration",
    "id": {
        "type": "Identifier",
        "name": "A"
    },
    "params": [
        {
            "type": "Identifier",
            "name": "b"
        }
    ],
    "body": {
        "type": "BlockStatement",
        "body": [
            {
                "type": "ExpressionStatement",
                "expression": {
                    "type": "AssignmentExpression",
                    "operator": "=",
                    "left": {
                        "type": "MemberExpression",
                        "computed": false,
                        "object": {
                            "type": "ThisExpression"
                        },
                        "property": {
                            "type": "Identifier",
                            "name": "b"
                        }
                    },
                    "right": {
                        "type": "Identifier",
                        "name": "b"
                    }
                }
            },
            {
                "type": "ReturnStatement",
                "argument": {
                    "type": "ThisExpression"
                }
            }
        ]
    }
  ]#
  
  let id = gen(n[0])
  var body: ESNode 
  let objdef = n[2]
  if objdef[2].kind == nkEmpty:
      return
  assert objdef[2].kind == nkRecList, $objdef[2].kind
  var props = newSeq[ESNode]()
  var pieces = newSeq[ESNode]()
  for el in objdef[2]: #el is identsdef
    if el.kind == nkIdentDefs: # skips the types
        if el[0].kind == nkIdent:
          let prop = gen(el[0])
          add props, prop
          add pieces, newExpressionStmt(
            newAsgnExpr(
              "=",
              newMemberExpr(
                newThisExpr(),
                prop,
                false,
                genSourceLoc(el[0])
              ),
              prop,
              genSourceLoc(el[0])
            ),
            genSourceLoc(el[0])
          )
  
  add pieces, newReturnStmt(newThisExpr())
  
  body = newBlockStmt(pieces,genSourceLoc(n))
  
  res = newFuncDecl(id,body,props,genSourceLoc(n))

proc newType*(n:PNode):ESNode =
  if n[0].typ.kind == tyObject:
    newObjType(n,result)
  else:
    print n
  
  echo treerepr(result)