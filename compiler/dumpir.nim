#
#
#           The Nim Compiler
#        (c) Copyright 2012 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module renders the ast after it has been through most of the compiler,
# just before it's passed to the codegen pass.

import
  options, ast, passes, pathutils, renderer, strutils, lineinfos, msgs, 
  astalgo,ropes, transf, trees, wordrecg

from modulegraphs import ModuleGraph, PPassContext

type
  TGen = object of PPassContext
    module: PSym
    config: ConfigRef
    graph: ModuleGraph
  PGen = ref TGen

  Backend = ref object of RootRef
    rendered: string
    mainFileId: FileIndex
    concretizedProcs: seq[PSym]

const nkGenSkippedKinds = { nkCommentStmt, nkTypeSection, nkPragma, nkEmpty, 
                            nkTemplateDef, nkFuncDef, nkProcDef, nkMethodDef, 
                            nkIteratorDef, nkMacroDef, nkIncludeStmt, 
                            nkImportStmt, nkExportStmt, nkExportExceptStmt, 
                            nkImportExceptStmt, nkImportAs, nkConverterDef}#, nkWhenStmt, nkWhenExpr }

const rDefFlags = {renderIr, renderIds, renderSyms,renderNoComments}

proc exportOrUsed(s: PSym): bool {.inline.} =
  ( s.flags.contains(sfExported) and 
    s.skipGenericOwner.flags.contains(sfMainModule)
  ) or s.flags.contains(sfUsed)


proc backend(g: PGen): Backend {.inline.} = Backend(g.graph.backend)

proc renderProcDef(g: PGen, n: PNode): string =
  if n[pragmasPos].kind != nkEmpty:
    if not findPragma(n[pragmasPos], wImportc).isNil:
      #echo "pragma importc found"
      # return early, importc don't have a body
      result = renderTree(n, rDefFlags)
      return
    else:
      echo "TODO: OTHER PRAGMAS"

  #echo g.config.treeToYaml(pragmas[0])
  #TODO:
  var prcBody = transformBody(g.graph, n[namePos].sym, cache=false)
  result = renderTree(n, rDefFlags)
  
  echo renderTree(prcBody, rDefFlags)

proc render(g: PGen, n: PNode): string =
  result = ""
  case n.kind:
  of nkGenSkippedKinds: return
  of nkDiscardStmt:
    if n[0].kind in nkCallKinds:
      result.add("discard ")
      result.add(g.render(n[0]))
    else: 
      echo "discarded smth, not a call"
  of nkCallKinds:
    if n[0].kind == nkSym: # lets print the def too
      #echo g.config.treeToYaml(n)
      if not (n[0].sym in g.backend.concretizedProcs):
        echo "concretizing ", n[0].sym.name.s
        # add the proc to rendered directly to avoid issues with `discard call(...)`
        g.backend.rendered.add("\n" & 
          g.renderProcDef(n[0].sym.ast) &
          "\n")
        g.backend.concretizedProcs.add(n[0].sym)
      result.add(renderTree(n[0], rDefFlags) & "( ")
      for i, otherarg in n.sons:
        if i == 0: continue
        result.add(g.render(otherarg) & ",")
      result[^1] = ')'
    else:
      echo "n[0] not a sym for nkCallKinds?"
  of nkAsgn, nkFastAsgn:
    if n[0].kind == nkSym:#lhs is symbol, eg x = 123
      discard #echo "SYM-RHS " , g.config.treeToYaml(n[1])  
    else: # some other lhs, eg x[1] = 123
      #echo "OTH-LHS ", g.config.treeToYaml(n[0])
      #echo "OTH-RHS ", g.config.treeToYaml(n[1])  
      discard # TODO: handle weird lhs
    result.add(renderTree(n[0], rDefFlags) & " = ") # print lhs
    result.add(g.render(n[1])) # analyzise, then print rhs
  of nkBracket:
    var tmp : string = "["
    for son in n.sons:
      tmp.add(" " & g.render(son) & ",")
    tmp[^1] = ']'
    if tmp.len > 1: # 0 is always [
      result.add(tmp)
  of nkBracketExpr:
    var tmp : string = g.render(n[0])
    # TODO: more than 1 arg in brackets
    tmp.add("[" & g.render(n[1]) & "]")
    if tmp.len > 1: # 0 is always [
      result.add(tmp)
  of nkBlockStmt:
    assert n.len == 2
    
    result.add("block " & renderTree(n[0], rDefFlags) & ":\n")
    for lin in g.render(n[1]).splitLines:
      result.add(lin.indent(2) & "\n")
  of nkWhileStmt:
    assert n.len == 2
    #echo g.config.treeToYaml(n)
    result.add("while " & renderTree(n[0], rDefFlags) & ":\n") # TODO: handle len
    for lin in g.render(n[1]).splitLines:
      result.add(lin.indent(2) & "\n")
  of nkStmtList:
    var tmp : string = ""
    for son in n.sons:
      var tmp2 = g.render(son)
      if tmp2.len > 0:
        tmp.add(tmp2)
        tmp.add("\n")
    if tmp.len > 0:
      result.add(tmp)
  of nkIdentDefs, nkConstDef: #TODO: handle rhs calls and other weirdness
    #echo g.config.treeToYaml(n)
    if n[0].kind == nkSym and n[0].sym.exportOrUsed:
      result.add(renderTree(n[0], rDefFlags) ) # print lhs
      #n[1] is the type, 99% of the time useless
      if not (n[1].kind == nkEmpty):
        result.add(" : " & renderTree(n[1], rDefFlags))
      elif not(n[2].kind == nkEmpty) and not n[2].typ.sym.isNil:
        result.add(" : " & n[2].typ.sym.name.s)
      elif not n[0].sym.typ.sym.isNil:
        result.add(" : " & n[0].sym.typ.sym.name.s)
      if not (n[2].kind == nkEmpty):
        result.add(" = " & g.render(n[2])) # analyzise, then print rhs
      #result = renderTree(n,rDefFlags)
    elif n[0].kind != nkSym:
      # not a symbol or _exported_ symbol
      echo "ident/costdef n[0] is not a symbol? ", n[0].kind
  of nkConstSection, nkVarSection, nkLetSection:
    #echo g.config.treeToYaml(n)
    let initial = if n.kind == nkConstSection: "const " 
                  elif n.kind == nkVarSection: "var " 
                  elif n.kind == nkLetSection: "let " 
                  else: "error: "
    for son in n.sons:
      # constdefs, identdefs
      var tmp = g.render(son)
      if tmp.len > 0:
        result.add(initial & tmp & "\n")
    #result = renderTree(n, {renderIr, renderIds, renderSyms,renderNoComments})
  of nkLiterals:
    echo "literal of kind: ", n.kind 
    result = renderTree(n,rDefFlags)
  #of nkForStmt, nkWhileStmt:
  #  echo "loop kind: ", n.kind 

  else:
    echo "kind: ", n.kind 
    result = renderTree(n,rDefFlags)

proc addRenderedPart(c: PPassContext, n: PNode): PNode =
  result = n
  let g = PGen(c)
  let b = Backend(g.graph.backend)
  # renderer -> a renderFlag: exportOrUsed to ignore useless syms
  
  var transfN = transformStmt(g.graph,g.module,n)
  var tmp = ""
  if transfN.kind notin nkGenSkippedKinds:
    tmp = g.render(transfN)
  #elif n.kind == nkP
  if tmp.isEmptyOrWhitespace(): return
  b.rendered.add("\n#### from: " & g.config.toFilename(n.info.fileIndex) & "\n")
  b.rendered.add(tmp.strip)

when not defined(nimHasSinkInference):
  {.pragma: nosinks.}

proc myClose(graph: ModuleGraph; b: PPassContext, n: PNode): PNode =
  var g = PGen(b)
  
  if passes.skipCodegen(g.config, n): return n
  if sfMainModule in g.module.flags:
    let outFile = g.config.prepareToWriteOutput()
    outFile.writeFile(Backend(g.graph.backend).rendered)

proc myOpen(graph: ModuleGraph; module: PSym): PPassContext {.nosinks.} =
  var g: PGen
  new(g)
  g.module = module
  g.config = graph.config
  g.graph = graph
  if graph.backend == nil:
    graph.backend = Backend(rendered: "")
  if module.flags.contains(sfMainModule):
    Backend(graph.backend).mainFileId = module.fileIdx
  result = g

const dumpirpass* = makePass(open = myOpen, process = addRenderedPart, myClose)

