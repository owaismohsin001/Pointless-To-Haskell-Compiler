from os import existsFile, existsDir, createDir, copyFile, commandLineParams
import location
import sets
import ASTNode
import tables
import nodeTypes
from tokenTypes as Tok import nil
import ptlsError
import strutils
import sequtils
import tokenizer
import parser

# Utility

func indent(str: string) : string =
  let newStr = "\n" & str & "\n"
  let indentlist = newStr.split("\n")
  let newIndexList = indentList.map(proc(x: string) : string = " "&x)
  return newIndexList.join("\n")

type
  Env* = ref object of RootObj
    parent: Env
    prelude: Env
    globals: Env
    defs: HashSet[string]

# Environment Methods
# --------------------------
proc createEnv(parent: Env = nil) : Env =
  var env = Env(parent: parent)
  let prelude = if isNil(parent): env
                elif isNil(parent.prelude): env
                else: parent.prelude
  let globals = if isNil(parent): env
                elif isNil(parent.globals): env
                else: parent.globals
  env.prelude = prelude
  env.globals = globals
  return env


proc addDefName(this: Env, name: string, loc: Location) =
  if this.defs.contains(name):
    let error = returnPtlsError("Name Error");
    error.msg = "Duplicate definition for name '" & name & "'"
    error.locs.add(loc)
    raise error;
  this.defs.incl(name)

proc spawn(this: Env) : Env = createEnv(this)

proc clone(this: Env) : Env =
  let copyEnv = createEnv(this.parent)
  for value in this.defs:
    copyEnv.defs.incl(value)
  return copyEnv

proc existsDefName(this: Env, name: string, loc: Location) =
  var searchEnv = this

  while searchEnv != nil:
    if searchEnv.defs.contains(name):
      return

    searchEnv = searchEnv.parent

  let error = returnPtlsError("Name Error");
  error.locs.add(loc)
  error.msg = "No definition for name '" & name & "'"
  raise error

# Forward Declarations
# -----------------------
proc compile(program: string, name: string, main: bool) : string
proc declare(env: Env, node: ASTNode, main: bool, traceLocs: seq[Location] = @[]) : bool
proc dispatch(immut_env: Env, immut_node: ASTNode, main: bool, immut_traceLocs: seq[Location] = @[]) : string
proc validate(env: Env, node: ASTNode, main: bool, traceLocs: seq[Location] = @[]) : bool{.discardable.}
proc eval[T](env: Env, node: ASTNode, fun: proc(env: Env, node: ASTNode, main: bool, immut_traceLocs: seq[Location] = @[]) : T = dispatch, main: bool = false) : T{.discardable.}

# Declarator, it forward declares functions
proc declare(env: Env, node: ASTNode, main: bool, traceLocs: seq[Location] = @[]) : bool =
  if node.NodeType == Program:
    for imp in node.imports:
      eval[bool](env, imp, fun = declare)
    for def in node.defs:
      eval[bool](env, def.lhs, fun = declare)
    return
  elif node.NodeType == Name:
    env.addDefName(node.identifier, node.location)
    return
  elif node.NodeType == Tuple:
    for elem in node.tuple_elems:
      env.addDefName(elem.identifier, node.location)
    return
  elif node.NodeType == Func:
    for param in node.func_params:
      env.addDefName(param.identifier, node.location)
    return
  elif node.NodeType == Import:
    env.addDefName(node.as_node.identifier, node.location)
    return
  else:
    quit "No declaration for " & $node.NodeType & " avalible"


# Undeclared variabele error
proc noDefinition(name : string, loc : Location) =
  let error = returnPtlsError("Name Error");
  error.msg = "No definition for name '" & name & "'"
  error.locs.add(loc)
  raise error

proc checkNoDefinition(env : Env, name : string, loc: Location) =
  existsDefName(env, name, loc)
  return

# Make sure no undeclared variables are used
proc validate(env: Env, node: ASTNode, main: bool, traceLocs: seq[Location] = @[]) : bool{.discardable.} =
  case node.NodeType:
    of Node.Array:
      for elem in node.array_elems:
        eval[bool](env, elem, fun = validate)
      return

    of Node.BinaryOp:
      eval[bool](env, node.bin_lhs, fun = validate)
      eval[bool](env, node.bin_rhs, fun = validate)
      return

    of Node.Bool:
      return

    of Node.Call:
      eval[bool](env, node.reference, fun = validate)
      for arg in node.refered:
        eval[bool](env, arg, fun = validate)
      return

    of Node.Conditional:
      eval[bool](env, node.ifClause, fun = validate)
      eval[bool](env, node.thenExpr, fun = validate)
      if node.elseExpr != nil:
        eval[bool](env, node.elseExpr, fun = validate)
      return

    of Node.Dict:
      for pair in node.dict_elems:
        eval[bool](env, pair.key, fun = validate)
        eval[bool](env, pair.val, fun = validate)
      return

    of Node.Export:
      for exp in node.exports:
        eval[bool](env, exp, fun = validate)
      return

    of Node.FieldRef:
      eval[bool](env, node.label, fun = validate)
      return

    of Node.Func:
      let new_env = env.spawn()
      eval[bool](new_env, node, fun = declare)
      eval[bool](new_env, node.fun_body, fun = validate)
      return

    of Node.Import:
      if not existsFile(node.path.strValue):
        let error = returnPtlsError("Import Error")
        error.msg = "No file at '" & node.path.strValue & "' exists"
        error.locs.add(node.location)
        raise error
      return

    of Node.Index:
      eval[bool](env, node.index_lhs, fun = validate)

    of Node.Label:
      return

    of Node.List:
      for elem in node.list_elems:
        eval[bool](env, elem, fun = validate)
      return

    of Node.Name:
      checkNoDefinition(env, node.identifier, node.location)
      return

    of Node.Number:
      return

    of Node.Object:
      let new_env = env.spawn()
      let programNode = ASTNode(NodeType: Node.Program, defs: node.obj_defs, export_name: nil)
      eval[bool](new_env, programNode, fun = declare)
      eval[bool](new_env, programNode, fun = validate)
      return

    of Node.Program:
      for n in node.imports:
        eval[bool](env, n, fun = validate)

      for def in node.defs:
        eval[bool](env, def.lhs, fun = validate)
        eval[bool](env, def.rhs, fun = validate)

      if not isNil(node.export_name):
        eval[bool](env, node.export_name, fun = validate)
      return

    of Node.Requires:
      eval[bool](env, node.requirement, fun = validate)
      eval[bool](env, node.required, fun = validate)

    of Node.Set:
      for elem in node.set_elems:
        eval[bool](env, elem, fun = validate)
      return

    of Node.String:
      return

    of Node.Throw:
      eval[bool](env, node.thrown_error, fun = validate)

    of Node.Try:
      eval[bool](env, node.trial_body, fun = validate)
      eval[bool](env, node.catch_condition, fun = validate)
      eval[bool](env, node.handler, fun = validate)

    of Node.Tuple:
      for elem in node.tuple_elems:
        eval[bool](env, elem, fun = validate)
      return

    of Node.UnaryOp:
      eval[bool](env, node.unary_node, fun = validate)
      return

    of Node.Where:
      let new_env = env.spawn()
      let programNode = ASTNode(NodeType: Node.Program, defs: node.where_clause.obj_defs, export_name: nil)
      eval[bool](new_env, programNode, fun = declare)
      eval[bool](new_env, programNode, fun = validate)
      eval[bool](new_env, node.where_body, fun = validate)
      return

    of Node.With:
      eval[bool](env, node.with_body, fun = validate)
      return

    of Node.Pair: quit "We hate pairs"
    of Node.Blank: quit "We hate blanks"
    of Node.Def: quit "We hate defs"

# Binary Operation handler
proc handleUnaryOp(env: Env, op: Tok.Tok, operandNode: ASTNode) : string =
  if op.str == Tok.Neg.str:
    let operand = eval[string](env, operandNode)
    return "ptlsNegate(" & operand & ")"
  elif op.str == Tok.Not.str:
    let operand = eval[string](env, operandNode)
    return "ptlsNot(" & operand & ")"

  quit op.str & "isn't quite an operator that I am familiar with"

proc handleBinaryOp(env: Env, op: Tok.Tok, lhsNode: ASTNode, rhsNode: ASTNode) : string =
  var res : string
  if op.str == Tok.Concat.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "createList " & lhsNode.location.haskellLoc & " (unterminatedListValue " & lhsNode.location.haskellLoc & " ((getList (" & lhs & ")) ++ (getList (" & rhs & "))))"

  elif op.str == Tok.Or.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsOr " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.And.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsAnd " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.Equals.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsEquals " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.NotEq.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsNotEquals " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.In.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsInside " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.LessThan.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsLessThan " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.LessEq.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsLessEquals " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.GreaterThan.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsGreaterThan " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.GreaterEq.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsGreaterEquals " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.Add.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsAdd " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.Sub.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsSub " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.Mul.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsMul " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.Div.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsDiv " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.Mod.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsMod " & "(" & lhs & ") (" & rhs & ")"

  elif op.str == Tok.Pow.str:
    let lhs = eval[string](env, lhsNode)
    let rhs = eval[string](env, rhsNode)
    res = "ptlsPow " & "(" & lhs & ") (" & rhs & ")"

  else:
    quit op.str & "isn't quite an operator that I am familiar with"

  return "(" & res & ")"

# The actual interpreter
# -----------------------
var depth = 0
var lastLoc : Location

proc eval[T](env: Env, node: ASTNode, fun: proc(env: Env, node: ASTNode, main: bool, immut_traceLocs: seq[Location] = @[]) : T = dispatch, main: bool = false) : T{.discardable.} =
  let maxDepth = 1000
  if depth > maxDepth:
    let error = returnPtlsError("Recursion Error")
    error.msg = "Max call depth " & $maxDepth & " exceeded"
    raise error
  try:
    return fun(env, node, main)
  except PtlsError:
    raise

proc update(env: Env, accessor: ASTNode, res: string): string =
  var new_res = res
  if accessor.NodeType == Node.Name:
    return res

  let lhs = eval[string](env, accessor[0])

  if accessor.NodeType == Node.Index:
    let index = eval[string](env, accessor[1])
    new_res =  "(updateIndex (" & lhs & ") (" & index & ") (" & new_res & "))"
  else:
    let name = $accessor.field.identifier
    new_res = "(updateField (" & lhs & ") (\"" & name & "\") (" & new_res & "))"
  return update(env, accessor[0], new_res)

proc dispatch(immut_env: Env, immut_node: ASTNode, main: bool, immut_traceLocs: seq[Location] = @[]) : string =
  var env = immut_env
  var node = immut_node
  while true:
    lastLoc = node.location
    case node.NodeType:
      of Node.Array:
        let ptls_array_seq = "[" & node.array_elems.map(proc(n: ASTNode) : string = eval[string](env, n)).join(", ") & "]"
        return "(createArray (" & node.location.haskellLoc & ") (" & ptls_array_seq & "))"

      of Node.BinaryOp:
        return handleBinaryOp(env, node.binary_op, node.bin_lhs, node.bin_rhs)

      of Node.Bool:
        let boolValue = if node.boolValue: "True"
                        else: "False"
        return "(createBool (" & node.location.haskellLoc & ") (" & boolValue & "))"

      of Node.Call:
        return "((" & eval[string](env, node.reference) & ") " &
          node.refered.map(proc(n: ASTNode) : string = "|> (" & eval[string](env, n) & ")").join(" ") &
          ")"

      of Node.Conditional:
        let condition = eval[string](env, node.ifClause)
        var str =  "if is_ptlsTrue(" & condition & ") then " & eval[string](env, node.thenExpr)
        if node.elseExpr == nil:
          str.add(" else error(show (createString (" & node.location.haskellLoc & ") \"No case matched\"))")
        else:
          str.add(" else " & eval[string](env, node.elseExpr))
        return "(" & str & ")"

      of Node.Dict:
        return "(createDict (" & node.location.haskellLoc & ") [" &
          node.dict_elems.map(proc(n: ASTNode) : string = "(" & eval[string](env, n.key) & ", " & eval[string](env, n.val) & ")").join(", ") & "])"

      of Node.FieldRef:
        let lhs = eval[string](env, node.label)
        let name = node.field.identifier
        return "(getProperty \"" & name & "\" " & lhs & ")"

      of Node.Func:
        var function = "("
        for param in node.func_params:
            function.add("createFunc (" & node.location.haskellLoc & ") (\\" & param.identifier & " -> ")
        function.add(eval[string](env, node.fun_body))
        for _ in 1..len(node.func_params):
          function.add(")")
        return function & ")"

      of Node.Index:
        let lhs = eval[string](env, node.index_lhs)
        let rhs = eval[string](env, node.index_rhs)
        return "(" & lhs & " `getIndex` " & rhs & ")"

      of Node.Label:
        return "(createLabel (" & node.location.haskellLoc & ") (\"" & node.labelValue & "\"))"

      of Node.List:
        let ptls_array_seq = "[" & node.list_elems.map(proc(n: ASTNode) : string = eval[string](env, n)).join(", ") & "]"
        return "(createList (" & node.location.haskellLoc & ") (" & ptls_array_seq & "))"

      of Node.Name:
        return node.identifier

      of Node.Number:
        return "(" & "createNumber (" & node.location.haskellLoc & ") (" & $node.numValue & ")" & ")"

      of Node.Object:
        var str = "(createObject (" & node.location.haskellLoc & ") (["
        var i = 0
        proc get(arr: seq[ASTNode], index: int) : ASTNode =
          if index < len(arr):
            return arr[index]
          return nil
        var both_sides : string
        while i<len(node.obj_defs):
          let n = node.obj_defs[i]
          if n.lhs.NodeType == Tuple:
            let lhs = "[" & n.lhs.tuple_elems.map(proc(n: ASTNode) : string = "\"" & n.identifier & "\"").join(", ") & "]"
            let rhs = "(value (lisVersion " & eval[string](env, n.rhs) & "))"
            both_sides = "] ++ (exceptZip " & n.rhs.location.haskellLoc & " " & lhs & " " & rhs & ") ++ ["
          else:
            let lhs = eval[string](env, n.lhs)
            both_sides = "(\"" & lhs & "\", " & eval[string](env, n.rhs) & ")"
          let next_node : ASTNode = node.obj_defs.get(i+1)
          let sep = if isNil(next_node): ""
                    elif next_node.lhs.NodeType == Tuple or n.lhs.NodeType == Tuple: ""
                    else: ", "
          str.add(both_sides & sep)
          i += 1
        str.add("]))")
        return str

      of Node.Program:
        let exports = node.export_name
        let imports = node.imports
        let defs = node.defs

        var evaluated_imports = ""
        var evaluated_defs = ""
        var evaluated_export = ""

        for importNode in imports:
          evaluated_imports.add(eval[string](env, importNode) & "\n")

        for importNode in imports:
          evaluated_imports.add(importNode.as_node.identifier & " = createObject (" & importNode.location.haskellLoc & ") (" & importNode.as_node.identifier.capitalizeAscii() & "___dts____.export)\n")

        for defNode in defs:
          if defNode.lhs.NodeType == Tuple:
            let typeDecls = defNode.lhs.tuple_elems.map(proc(n: ASTNode) : string = n.identifier & " :: Value").join("\n")
            let lhs = "(" & defNode.lhs.tuple_elems.map(proc(n: ASTNode) : string = n.identifier).join(", ") & ")"
            let faliureMessage = "error (show (createException (createString (" & defNode.rhs.location.haskellLoc & ") (\"Can't destructure tuple to " & $len(defNode.lhs.tuple_elems) & " names\"))))"
            let rhs = "case fromDynamic (tup " & eval[string](env, defNode.rhs) & ") of \n Nothing -> " & faliureMessage &
              "\n Just x -> x"
            evaluated_defs.add(typeDecls & "\n" & lhs & " = " & rhs & "\n")
          else:
            let lhs = eval[string](env, defNode.lhs)
            evaluated_defs.add(lhs & " = " & eval[string](env, defNode.rhs) & "\n")

        if exports == nil:
          var exp : seq[string] = @[]
          for name in env.defs:
            exp.add("(" & "\"" & name & "\"" & ", " & name & ")")
          evaluated_export = "export = [" & exp.join(", ") & "]"
        else:
          var exp = exports.exports.map(proc(n: ASTNode) : string = n.identifier & ", " & "\"" & n.identifier & "\"").join(", ")
          evaluated_export = "export = [" & exp & "]"

        let between = if main: "main = do\n case output of\n  PtlsException e -> putStrLn (show (createException e))\n  otherwise -> putStrLn (show (isPtlsList output))"
                      else: ""
        let fname = node.location.path.split("/")[len(node.location.path.split("/")) - 1]
        let modDecl = if main: ""
                      else: "module " & capitalizeAscii(fname.split(".")[0]) & " (export) where \n\n"
        return modDecl & "import PtlsRuntime\n" & evaluated_imports & "\n" &
        evaluated_defs & "\n" & evaluated_export & "\n\n" & between & "\n"

      of Node.Requires:
        let condition = eval[string](env, node.requirement)
        let action = eval[string](env, node.required)
        return "(if is_ptlsTrue(" & condition & ") then " & action & " else createException (createString (" & node.location.haskellLoc & ") \"Unmet Condition\"))"

      of Node.Set:
        return "(createSet (" & node.location.haskellLoc & ") ([" & node.set_elems.map(proc(n: ASTNode) : string = eval[string](env, n)).join(", ") & "])" & ")"

      of Node.String:
        return "(createString (" & node.location.haskellLoc & ") " & "\"" & node.strValue & "\"" & ")"

      of Node.Throw:
        let value = eval[string](env, node.thrown_error)
        return "(createException(" & value & "))"

      of Node.Try:
        let trial_body = eval[string](env, node.trial_body)
        let catch_condition = eval[string](env, node.catch_condition)
        let handler = eval[string](env, node.handler)
        return "\n" & """
  let
    error_prone_res = """ & trial_body & "\n" & """
  in
    case error_prone_res of
      PtlsException e -> if is_ptlsTrue(((""" & catch_condition & """)) |> e) then ((""" & handler & """) |> e) else error_prone_res
      otherwise -> error_prone_res
        """

      of Node.Tuple:
        return "(createTuple (" & node.location.haskellLoc & ") (toDyn (" & node.tuple_elems.map(proc(n: ASTNode) : string = eval[string](env, n)).join(", ") & ")) " & $len(node.tuple_elems) &
          " " & "[" & node.tuple_elems.map(proc(n: ASTNode) : string = eval[string](env, n)).join(", ") & "]" & ")"

      of Node.UnaryOp:
        return handleUnaryOp(env, node.op, node.unary_node)

      of Node.Where:
        var defs = ""
        eval[bool](env.spawn(), ASTNode(NodeType: Node.Program, defs: node.where_clause.obj_defs, imports: @[], export_name: nil), fun = declare)
        for defNode in node.where_clause.obj_defs:
          if defNode.lhs.NodeType == Tuple:
            let typeDecls = defNode.lhs.tuple_elems.map(proc(n: ASTNode) : string = n.identifier & " :: Value").join("\n")
            let lhs = "(" & defNode.lhs.tuple_elems.map(proc(n: ASTNode) : string = n.identifier).join(", ") & ")"
            let faliureMessage = "error (show (createException (createString (" & defNode.rhs.location.haskellLoc & ") \"Can't destructure tuple to " & $len(defNode.lhs.tuple_elems) & " names\")))"
            let rhs = "case fromDynamic (tup " & eval[string](env, defNode.rhs) & ") of \n Nothing -> " & faliureMessage &
              "\n Just x -> x"
            defs.add(typeDecls & "\n" & lhs & " = " & rhs & "\n")
          else:
            let lhs = eval[string](env, defNode.lhs)
            defs.add(lhs & " = " & eval[string](env, defNode.rhs) & "\n")
        return "\n let" & indent(indent(defs)) & "in" & indent(indent(eval[string](env, node.where_body)))

      of Node.With:
        let newEnv = env.spawn()
        var all_defs = @["meta__1 = " & eval[string](env, node.with_body)]
        var newest_num = "1"
        let values = node.with_defs.map(proc(n: ASTNode) : string = eval[string](newEnv, n.rhs))
        var index = 0
        for def in node.with_defs:
          let variable_current_def = values[index]
          let new_thing = update(newEnv, def.lhs, variable_current_def).replace("$", "meta__" & newest_num)
          newest_num.add("1")
          all_defs.add("meta__" & newest_num & " = " & new_thing)
          index += 1
        return "\n let" & indent(indent(all_defs.join("\n"))) & "\n in\n  " & "meta__" & newest_num

      of Node.Import:
        let split_name = node.path.strValue.split(".")[0].capitalizeAscii()
        let chars = @(readFile(node.path.strValue)).filter(proc(x: char) : bool = x != '\r').join("")
        let compiled_text = compile(chars, node.path.strValue, false)
        if not existsDir("output"):
          createDir("output")
        writeFile("output/" & split_name & ".hs", compiled_text)
        let as_name = node.as_node.identifier.capitalizeAscii() & "___dts____"
        return "import qualified " & split_name & " as " & as_name & "\n"

      of Node.Pair: quit "We hate pairs"
      of Node.Blank: quit "We hate blanks"
      of Node.Def: quit "We hate defs"
      of Node.Export: quit "We hate exports"

proc compile(program: string, name: string, main: bool) : string =
  let toks = getToks(program, name)
  let ast = makeast(toks)
  let env = createEnv()
  try:
    discard eval[bool](env, ast, fun = declare)
    discard eval[bool](env, ast, fun = validate)
    if main:
      checkNoDefinition(env, "output", ast.location)
  except PtlsError as err:
    echo err.locs.deduplicate.join("\n")
    raise
  return eval[string](env, ast, main = main)

let commands = commandLineParams().map(proc(x: TaintedString) : string = $x)
if len(commands) != 1:
  quit "Wrong amount of parameters, the correct format is, [compiler-name] [file-name]"

if not existsFile(commands[0]):
  let error = returnPtlsError("IO Error")
  error.msg = "The file " & commands[0] & " doesn't exist"
  raise error

let name = commands[0].split(".")[0]
let program = @(readFile(commands[0])).filter(proc(x: char) : bool = x!='\r').join("")
let compiled_text = compile(program, name, true)
if not existsDir("output"):
  createDir("output")
copyFile("PtlsRuntime.hs", "output/PtlsRuntime.hs")
writeFile("output/" & name & ".hs", compiled_text)
echo compiled_text
