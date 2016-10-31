namespace Microsoft.P2Boogie
module Translator =

  open System
  open Syntax
  open Helper
  open Common
  open ProgramTyping
  open System.CodeDom.Compiler

  (* Translation of normalized side-effect-free programs to Boogie *)
  
  let Typmap = ref Map.empty
  let TypmapIndex = ref 0

  let GetTypeIndex t =
    if Map.containsKey t !Typmap then Map.find t !Typmap
    else begin
      let ret = !TypmapIndex
      Typmap := Map.add t ret !Typmap
      TypmapIndex := ret + 1
      ret
    end

  let GetAllTypes () =
    Map.fold (fun state key _ -> Set.add key state) Set.empty !Typmap

  let (monitorToStartState: Map<string, int> ref) = ref Map.empty
  
  let translateType t =
    match t with
    | Null -> "PrtTypeNull"
    | Bool -> "PrtTypeBool"
    | Int -> "PrtTypeInt"
    | Machine -> "PrtTypeMachine"
    | Type.Event -> "PrtTypeEvent"
    | Type.NamedTuple(_) -> raise NotDefined
    | Type.ModelType s -> sprintf "PrtTypeModel%s" s
    | Any -> raise NotDefined
    | Type.Tuple(ls) -> sprintf "PrtTypeTuple%d" (List.length ls)
    | Type.Seq(t1) -> sprintf "PrtTypeSeq%d" (GetTypeIndex t)
    | Type.Map(t1, t2) -> sprintf "PrtTypeMap%d" (GetTypeIndex t)

  let rec translateExpr (G:Map<string, Type>) (evMap: Map<string, int>) expr =
    match expr with
    | Nil -> "null"
    | Expr.ConstInt(i) -> sprintf "PrtConstructFromInt(%d)" i
    | Expr.ConstBool(b) -> if b then "PrtTrue" else "PrtFalse"
    | Expr.This -> "PrtConstructFromMachineId(thisMid)"
    | Expr.Default t when t = Null || t = Machine || t = Type.Event || t = Any -> "null"
    | Expr.Default Int -> "PrtConstructFromInt(0)"
    | Expr.Default Bool -> "PrtFalse"
    | Expr.Event s -> sprintf "PrtConstructFromEventId(%d)" (Map.find s evMap)
    | Expr.Var(v) -> v
    | Expr.Bin(op, e1, e2) when  isIntop(op) -> sprintf "PrtConstructFromInt(PrtFieldInt(%s) %s PrtFieldInt(%s))" (translateExpr G evMap e1) (printBinop op) (translateExpr G evMap e2)
    | Expr.Bin(op, e1, e2) when  isRelop(op) -> sprintf "PrtConstructFromBool(PrtFieldInt(%s) %s PrtFieldInt(%s))" (translateExpr G evMap e1) (printBinop op) (translateExpr G evMap e2)
    | Expr.Bin(op, e1, e2) when  isBoolop(op) -> sprintf "PrtConstructFromBool(PrtFieldBool(%s) %s PrtFieldBool(%s))" (translateExpr G evMap e2) (printBinop op) (translateExpr G evMap e2)
    | Expr.Bin(op, e1, e2) when  isComparison(op) -> raise NotDefined
    | Expr.Bin(Idx, e1, e2) -> raise NotDefined
    | Expr.Bin(In, e1, e2) -> raise NotDefined
    | Expr.Un(Not, e) -> sprintf "PrtConstructFromBool(!PrtFieldBool(%s))" (translateExpr G evMap e)
    | Expr.Un(Neg, e) -> sprintf "PrtConstructFromInt(0 - PrtFieldInt(%s))" (translateExpr G evMap e)
    | Expr.Un(Sizeof, e) when isSeq (typeof e G) -> sprintf "PrtConstructFromInt(PrtFieldSeqSize(%s))" (translateExpr G evMap e)
    | Expr.Un(Sizeof, e) -> sprintf "PrtConstructFromInt(PrtFieldMapSize(%s))" (translateExpr G evMap e)
    | Expr.Dot(e, f) -> sprintf "PrtFieldTuple%d(%s)" f (translateExpr G evMap e)
    | _ -> raise NotDefined

  let translateMachineExpr G evMap m =
    match m with
    | Expr.This   -> "thisMid"
    | _ -> sprintf "PrtFieldMachine(%s)" (translateExpr G evMap m)

  let translateEventExpr (sw: IndentedTextWriter) G evMap e plExpr =
    match e with
    | Expr.Event(ev) -> sprintf "%d" (Map.find ev evMap)
    | _ ->
      begin 
        sw.WriteLine("call tmpEventID := AssertPayloadDynamicType({0}, {1});", (translateExpr G evMap e), plExpr)
        "tmpEventID"
      end

  let typesAsserted = ref Set.empty

  let rec translateAssign (sw: IndentedTextWriter) G evMap lval expr  =
    
    let genRhsValue e G =
        let rhsVar = "tmpRhsValue" in
        sw.WriteLine("{0} := {1};", rhsVar, (translateExpr G evMap e))
        rhsVar
    in
    let getLhsVar lval = match lval with
                            | Lval.Var(v) -> v
                            | _ -> raise NotDefined
    in
    let rec setTypesAsserted t =
        typesAsserted := Set.add t !typesAsserted
        match t with
        | Type.Tuple ts -> List.iter setTypesAsserted ts
        | _ -> ()
    match (lval, expr) with
    | _, Expr.Cast(e, t) ->
      begin
        (* evaluate rhs *)
        let rhsVar = genRhsValue e G in
        (* generate type assertion *)
        setTypesAsserted t
        sw.WriteLine("call AssertIsType{0}({1});", (GetTypeIndex t), rhsVar)
        (* the assignment *)
        sw.WriteLine("{0} := {1};", (getLhsVar lval), rhsVar)
      end
    | _, Expr.Tuple(es) ->
      begin
        for i = 0 to (List.length es) - 1 do
          let ei = (List.item i es) in
            sw.WriteLine("tmpRhsValue_{0} := {1};", i, (translateExpr G evMap ei))

        sw.WriteLine("call {0} := AllocatePrtRef();", (getLhsVar lval))
        sw.WriteLine("assume PrtDynamicType({0}) == PrtTypeTuple{1};", (getLhsVar lval), (List.length es))

        for i = 0 to (List.length es) - 1 do
          sw.WriteLine("assume PrtFieldTuple{0}({1}) == tmpRhsValue_{2};", i, (getLhsVar lval), i)
      end
    | _, Expr.Call(callee, args) ->
      begin
        let a = args |> List.map (translateExpr G evMap) |> String.concat ", " 
        sw.WriteLine("call {0} := {1}({2});", (getLhsVar lval), callee, a)
      end
    | _, Expr.Default(Seq(t)) ->
      begin
        sw.WriteLine("call {0} := AllocatePrtRef();", (getLhsVar lval))
        sw.WriteLine("assume PrtDynamicType({0}) == PrtTypeSeq{1};", (getLhsVar lval), (GetTypeIndex (Seq(t))))
        sw.WriteLine("assume PrtFieldSeqSize({0}) == 0;", (getLhsVar lval))
      end
    | _, Expr.Default(Map(t1, t2)) ->
      begin
        sw.WriteLine("call {0} := AllocatePrtRef();", (getLhsVar lval))
        sw.WriteLine("assume PrtDynamicType({0}) == PrtTypeMap{1};", (getLhsVar lval), (GetTypeIndex (Map(t1, t2))))
        sw.WriteLine("assume PrtFieldMapSize({0}) == 0;", (getLhsVar lval))
      end
    | _, Expr.Bin(Idx, e1, e2) ->
      begin
        match isMap (typeof e1 G) with
        | true ->  sw.WriteLine("call {0} := ReadMap({1}, {2});", (getLhsVar lval), (translateExpr G evMap e1), (translateExpr G evMap e2))
        | false -> sw.WriteLine("assert SeqIndexInBounds({0}, PrtFieldInt({1})); {2} := ReadSeq({3}, PrtFieldInt({4}));", (translateExpr G evMap e1), (translateExpr G evMap e2), (getLhsVar lval), (translateExpr G evMap e1), (translateExpr G evMap e2))
      end
    | _, Expr.Bin(In, e1, e2) ->
      sw.WriteLine("call {0} := MapContainsKey({1}, {2});", (getLhsVar lval), (translateExpr G evMap e1), (translateExpr G evMap e2))
    | _, Expr.Bin(Eq, e1, e2) ->
      sw.WriteLine("call {0} := PrtEquals({1}, {2});", (getLhsVar lval), (translateExpr G evMap e1), (translateExpr G evMap e2))
    | _, Expr.Un(Keys, e) ->
      begin
        sw.WriteLine("call {0} := MapGetKeys({1});", (getLhsVar lval), (translateExpr G evMap e))
        sw.WriteLine("assume PrtDynamicType({0}) == PrtTypeSeq{1};", (getLhsVar lval), (GetTypeIndex (Map.find (getLhsVar lval) G)))
      end
    | _, Expr.Un(Values, e) ->
      begin
        sw.WriteLine("call {0} := MapGetValues({1});", (getLhsVar lval), (translateExpr G evMap e))
        sw.WriteLine("assume PrtDynamicType({0}) == PrtTypeSeq{1};", (getLhsVar lval), (GetTypeIndex (Map.find (getLhsVar lval) G)))
      end
    | _, Expr.Nondet ->
      sw.WriteLine("havoc {0};", (getLhsVar lval))
    | Lval.Var(v), Expr.New(m, arg) ->
        sw.WriteLine("call {0} := newMachine_{1}({2});", v, m, translateExpr G evMap arg)
    | Lval.Index(Lval.Var(lhsVar), e), _ when isSeq (typeofLval (Lval.Var(lhsVar)) G) ->
      sw.WriteLine("call {0} := WriteSeq({1}, PrtFieldInt({2}), {3});", lhsVar, lhsVar, (translateExpr G evMap e), (translateExpr G evMap expr))
    | Lval.Index(Lval.Var(lhsVar), e), _ ->
      sw.WriteLine("call {0} := WriteMap({1}, {2}, {3});", lhsVar, lhsVar, (translateExpr G evMap e), (translateExpr G evMap expr))
    | Lval.Dot(_), _ -> raise NotDefined
    | _, _ ->
      sw.WriteLine("{0} := {1};", (getLhsVar lval), (translateExpr G evMap expr))

  let translateInsert (sw:IndentedTextWriter) G evMap v e1 e2 =
    match isSeq (typeof (Expr.Var(v)) G) with
    | true -> sw.WriteLine("call {0} := InsertSeq({1}, PrtFieldInt({2}), {3});", v, v, (translateExpr G evMap e1), (translateExpr G evMap e2))
    | false -> sw.WriteLine("call {0} := InsertMap({1}, PrtFieldInt({2}), {3});", v, v, (translateExpr G evMap e1), (translateExpr G evMap e2))

  let translateRemove (sw:IndentedTextWriter) G evMap v e1 =
    match isSeq (typeof (Expr.Var(v)) G) with
    | true -> sw.WriteLine("call {0} := RemoveSeq({1}, PrtFieldInt({2}));", v, v, (translateExpr G evMap e1))
    | false -> sw.WriteLine("call {0} := RemoveMap({1}, PrtFieldInt({2}));", v, v, (translateExpr G evMap e1))

  let rec translateStmt (sw: IndentedTextWriter) G (stateToInt: Map<string, int>) (cm: string) (evMap: Map<string, int>) stmt =
    
    let translateCase (e, st) =
      sw.WriteLine("if(event == {0})", (Map.find e evMap))
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
      translateStmt sw G stateToInt cm evMap st
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")
      sw.Write("else ")
    match stmt with
    | Assign(l, e) -> translateAssign sw G evMap l e
    | Insert(Lval.Var(v), e1, e2) -> translateInsert sw G evMap v e1 e2
    | Remove(Lval.Var(v), e1) -> translateRemove sw G evMap v e1
    | Assume(e) -> sw.WriteLine("assume PrtFieldBool({0});", (translateExpr G evMap e))
    | Assert(e) -> sw.WriteLine("assert PrtFieldBool({0});", (translateExpr G evMap e))
    | NewStmt(m, e) -> sw.WriteLine("call tmpRhsValue := newMachine_{0}({1});", m, (translateExpr G evMap e))
    | Raise(e, a) ->
      begin
        let plExpr = (translateExpr G evMap a)
        let eExp = (translateEventExpr sw G evMap e plExpr)
        sw.WriteLine("eventRaised := true;")
        sw.WriteLine("raisedEvent := {0};", eExp)
        sw.WriteLine("raisedEventPl := {0};", plExpr)
      end
    | Send(m, e, arg) ->
      begin
        let plExpr = (translateExpr G evMap arg)
        let eExp = (translateEventExpr sw G evMap e plExpr)
        sw.WriteLine("call send({0}, {1}, {2});", (translateMachineExpr G evMap m), eExp, plExpr)
      end
    | Skip(_,-1,_) -> ignore true
    | Skip(f, l, c) -> sw.WriteLine("assume {{:sourceloc \"{0}\", {1}, {2}}} true;", f, l, c)
    | While(c, st) ->
      begin
        sw.WriteLine("while(PrtFieldBool({0}))", (translateExpr G evMap c))
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        translateStmt sw G stateToInt cm evMap st
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
      end
    | Ite(c, i, e) ->
      begin
        sw.WriteLine("if(PrtFieldBool({0}))", (translateExpr G evMap c))
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        translateStmt sw G stateToInt cm evMap i
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
        sw.WriteLine("else")
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        translateStmt sw G stateToInt cm evMap e
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
      end
    | SeqStmt(ls) -> List.iter (translateStmt sw G stateToInt cm evMap) ls
    | Receive(ls) ->
      begin
        sw.WriteLine("yield;")
        sw.WriteLine("call event, payload := Dequeue();")
        List.iter translateCase ls
        sw.WriteLine("")
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        sw.WriteLine("assert false;")
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
      end
    | Pop ->
      begin
        if cm = "" then raise NotDefined
        sw.WriteLine("call {0}_CallExitAction();", cm)
        sw.WriteLine("call StateStackPop();")
      end
    | Return(None) -> sw.WriteLine("return;")
    | Return(Some(e)) ->
      begin
        sw.WriteLine("ret := {0};", (translateExpr G evMap e))
        sw.WriteLine("return;")
      end
    | Monitor(e, arg) ->
      begin
        let plExpr = (translateExpr G evMap arg)
        let eExp = (translateEventExpr sw G evMap e plExpr)
        sw.WriteLine("call monitor({0}, {1});", eExp, plExpr)
      end
    | FunStmt(f, el, v) ->
      begin
        let args = el |> List.map (translateExpr G evMap) |> String.concat ", "
        let lhs = match v with
                  | None -> ""
                  | Some(x) -> sprintf " %s := " x
        sw.WriteLine("call {0}{1}({2});", lhs, f, args)
      end
    | Goto(s, e) -> 
      begin
        if cm = "" then raise NotDefined
        sw.WriteLine("payload := {0};", translateExpr G evMap e)
        sw.WriteLine("call {0}_CallExitAction();", cm)
        sw.WriteLine("call {0}_CallEntryAction({1}, payload);", cm, (Map.find s stateToInt))
        sw.WriteLine("CurrState := {0};", Map.find s stateToInt)
        sw.WriteLine("goto {0};", s)
      end
    | _ -> raise NotDefined

  let fprintfnComment (sw:IndentedTextWriter) x =
    sw.WriteLine("// " + x)

  let printEquals (sw: IndentedTextWriter) maxFields =
    fprintfn sw "// Equals
procedure PrtEquals(a: PrtRef, b: PrtRef) returns (v: PrtRef)
{
    var ta, tb: PrtType;

    if(a == b) { v := PrtTrue; return; }

    ta := PrtDynamicType(a);
    tb := PrtDynamicType(b);

    if(ta != tb) { v := PrtFalse; return; }
    if(ta == PrtTypeInt) { v := PrtConstructFromBool(PrtFieldInt(a) == PrtFieldInt(b)); return; }
    if(ta == PrtTypeBool) { v := PrtConstructFromBool(PrtFieldBool(a) == PrtFieldBool(b)); return; }
    if(ta == PrtTypeMachine) { v := PrtConstructFromBool(PrtFieldMachine(a) == PrtFieldMachine(b)); return; }
    if(ta == PrtTypeEvent) { v := PrtConstructFromBool(PrtFieldEvent(a) == PrtFieldEvent(b)); return; }
    "

    for i = 1 to maxFields do
        sw.WriteLine("    if(ta == PrtTypeTuple{0}) {{ call v := PrtEqualsTuple{1}(a,b); return; }}", i, i)

    fprintfn sw "
    // Map, Seq type
    assume false;
  }
    "
    for i = 1 to maxFields do
      begin
        sw.WriteLine("procedure PrtEqualsTuple{0}(x: PrtRef, y: PrtRef) returns (v: PrtRef)", i)
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        for j = 0 to (i-1) do
          begin
            sw.WriteLine("call v := PrtEquals(PrtFieldTuple{0}(x), PrtFieldTuple{1}(y));", j, j)
            if j <> (i-1) then sw.WriteLine("if(v == PrtFalse) { return; }")
          end
        sw.WriteLine("return;")
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
      end

  let printTypeCheck (sw:IndentedTextWriter) t =
    let tindex =  GetTypeIndex t  in
    sw.WriteLine("// Type {0}", (printType t))
    sw.WriteLine("procedure AssertIsType{0}(x: PrtRef) ", tindex)
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    match t with
    | Null -> raise NotDefined
    | Any -> raise NotDefined
    | Bool
    | Seq(_)
    | Map(_, _)
    | Int -> sw.WriteLine("assert PrtDynamicType(x) == {0};", (translateType t))
    | Machine
    | Type.Event -> sw.WriteLine("assert PrtDynamicType(x) == {0} || PrtIsNull(x);", (translateType t))
    | Type.NamedTuple(_) -> raise NotDefined
    | Type.ModelType s -> sw.WriteLine("assert PrtDynamicType(x) == PrtTypeModel{0};", s)
    | Type.Tuple ts ->
      begin
        sw.WriteLine("assert PrtDynamicType(x) == PrtTypeTuple{0};", (List.length ts))
        for i = 0 to ((List.length ts) - 1) do
          begin 
            let ti = List.item i ts in
            sw.WriteLine("call AssertIsType{0}(PrtFieldTuple{1}(x));", (GetTypeIndex ti), i)
          end
      end
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  let getVars attr (vdList: VarDecl list) =
    List.map (fun(vd: VarDecl) -> sprintf "var%s %s: PrtRef; // %s" attr vd.Name (printType vd.Type)) vdList

  let getEventMaps d trans hasDefer hasIgnore (events: Map<string, int>) =
    let regEvents = ref(events |> Map.toSeq |> Seq.map (fun (k, v) -> (v, false)) |> Map.ofSeq)
    let igEvents  = ref(events |> Map.toSeq |> Seq.map (fun (k, v) -> (v, false)) |> Map.ofSeq)
    let defEvents = ref(events |> Map.toSeq |> Seq.map (fun (k, v) -> (v, false)) |> Map.ofSeq)
    for l in d do
      match l with
      | DoDecl.T.Ignore(e) ->
        begin
          let evId = events.[e]
          regEvents := Map.add evId true !regEvents
          igEvents  := Map.add evId true !igEvents
        end
      | DoDecl.T.Defer(e) ->
        begin
          let evId = events.[e]
          regEvents := Map.add evId true !regEvents
          defEvents := Map.add evId true !defEvents
        end
      | DoDecl.T.Call(e, _) ->
        begin
          let evId = events.[e]
          regEvents := Map.add evId true !regEvents
        end
    for l in trans do
      match l with
      | TransDecl.T.Call(e,_,_) | TransDecl.T.Push(e,_) ->
        begin
          let evId = events.[e]
          regEvents := Map.add evId true !regEvents
        end
    let l1 = [!regEvents] @ (if hasIgnore then [!igEvents] else [])
              @ (if hasDefer then [!defEvents] else [])
    let l2 = ["registerEvents"] @ (if hasIgnore then ["ignoreEvents"] else [])
              @ (if hasDefer then ["deferEvents"] else [])

    List.zip l1 l2

  //TODO Come back!
  let printEvDict (sw:IndentedTextWriter) (state: int) (evDict: Map<int, bool>, name: string)=
    Map.iter (fun k v ->sw.WriteLine("{0}[{1}][{2}] := {3};", name, state, k, if v then "true" else "false")) evDict

  let translateFunction (sw: IndentedTextWriter) G (stateToInt: Map<string, int>) cm evMap (fd: FunDecl) =
    let formals = fd.Formals |> List.map (fun(v: VarDecl) -> "actual_" + v.Name + ": PrtRef") |> String.concat ", "
    let ret = if fd.RetType.IsSome then " returns (ret: PrtRef)" else ""
    sw.WriteLine("procedure {0}({1}){2}", fd.Name, formals, ret)
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    fd.Formals |> List.map (fun(v) -> "var " + v.Name + ": PrtRef;")  |> List.iter (fun(s) -> sw.WriteLine(s))
    getVars "" fd.Locals |> List.iter (fun(x) -> sw.WriteLine("{0}", x))
    
    sw.WriteLine("var event: int;")
    sw.WriteLine("var payload: PrtRef;")
    
    fd.Formals |> List.map (fun(v) -> v.Name + ":= actual_" + v.Name + ";") |> List.iter (fun(s) -> sw.WriteLine(s))
    
    let G' = mergeMaps G (fd.VarMap)
    List.iter (translateStmt sw G' stateToInt  cm evMap) fd.Body
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  let translateDos (sw: IndentedTextWriter) evMap (d: DoDecl.T) =
    begin
      match d with
      | DoDecl.T.Call(e, f) ->
        begin
          sw.WriteLine("if(event == {0}) //{1}", (Map.find e evMap), e)
          sw.WriteLine("{")
          sw.Indent <- sw.Indent + 1
          sw.WriteLine("call {0}(payload);", f)
          sw.Indent <- sw.Indent - 1
          sw.WriteLine("}")
        end
      | DoDecl.T.Ignore(e) -> sw.WriteLine("if(event == {0}) {{}} //{1} ignored.", (Map.find e evMap), e)
      | DoDecl.T.Defer(e) -> sw.WriteLine("if(event == {0}) {{}} //{1} deferred.", (Map.find e evMap), e)
      sw.Write("else ")
    end
  let translateTransitions (sw: IndentedTextWriter) (mach: MachineDecl) src (stateToInt:Map<string, int>) (evMap: Map<string,int>) (t: TransDecl.T) =
    begin 
      match t with
      | TransDecl.T.Call(e, d, f) ->
        begin
          sw.WriteLine("if(event == {0}) // {1}", (Map.find e evMap), e)
          sw.WriteLine("{")
          sw.Indent <- sw.Indent + 1;
          sw.WriteLine("call {0}_CallExitAction();", mach.Name)
          sw.WriteLine("call {0}(payload);", f)
          sw.WriteLine("CurrState := {0};", Map.find d stateToInt)
          sw.WriteLine("call {0}_CallEntryAction({1}, payload);", mach.Name, Map.find d stateToInt)
          sw.Indent <- sw.Indent - 1
          sw.WriteLine("}")
        end
      |TransDecl.T.Push(e, d) ->
        begin
          sw.WriteLine("if(event == {0}) // {1}", (Map.find e evMap), e)
          sw.WriteLine("{")
          sw.Indent <- sw.Indent + 1
          sw.WriteLine("call StateStackPush({0});", (Map.find src stateToInt))
          sw.WriteLine("CurrState := {0};", (Map.find d stateToInt))
          sw.WriteLine("call {0}_CallEntryAction({1}, payload);", mach.Name, Map.find d stateToInt)
          sw.Indent <- sw.Indent - 1
          sw.WriteLine("}")
        end
      sw.Write("else ")
    end
  let haltHandled (state: StateDecl) =
    let haltHandledInDo (d: DoDecl.T) =
      match d with
      | DoDecl.T.Defer(e) ->  e = "halt"
      | DoDecl.T.Ignore(e) -> e = "halt"
      | DoDecl.T.Call(e, _) -> e = "halt"

    let haltHandledInTrans (t: TransDecl.T) =
      match t with
      | TransDecl.T.Push(e, _) ->  e = "halt"
      | TransDecl.T.Call(e,_,_) -> e = "halt"

    let hd = List.fold (fun acc d -> acc || (haltHandledInDo d)) false state.Dos
    let ht = List.fold (fun acc t -> acc || (haltHandledInTrans t)) false state.Transitions
    ht || hd

  let translateState (sw: IndentedTextWriter) mach (stateToInt:Map<string, int>) hasDefer hasIgnore (evMap: Map<string,int>) (state: StateDecl) =
    sw.WriteLine("if(CurrState == {0})", (Map.find state.Name stateToInt))
    sw.WriteLine("{")
    sw.WriteLine("  {0}:", state.Name)
    sw.Indent <- sw.Indent + 1
    List.iter (translateDos sw evMap) state.Dos
    List.iter (translateTransitions sw mach state.Name stateToInt evMap) state.Transitions
    if (not (haltHandled state)) then
      begin
        sw.WriteLine("if(event == {0}) //halt", (Map.find "halt" evMap))
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        sw.WriteLine("return;")
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
        sw.Write("else")
      end
    
    sw.WriteLine()
    //Raise exception for unhandled event.
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("assert false;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    sw.Write("else ")

  let createNewMachineFunction (sw: IndentedTextWriter) G (evMap: Map<string,int>) (md: MachineDecl) =    
    let m = md.Name
    sw.WriteLine("procedure newMachine_{0}(entryArg: PrtRef) returns (m: PrtRef)", m)
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("var tmp: int;")
    sw.WriteLine("machineCounter := machineCounter + 1;")
    sw.WriteLine("tmp := machineCounter;")
    sw.WriteLine("call InitializeInbox(tmp);")
    sw.WriteLine("// Generate Queue Constraint Mappings")
    let qc =
      match md.QC with
      | Some(Card.Assert(i)) -> sprintf "%d" i, "0 - 1"
      | Some(Card.Assume(i)) -> "0 - 1", sprintf "%d" i
      | None -> "0 - 1", "0 - 1"
    sw.WriteLine("machineToQCAssert[tmp] := {0};", (fst qc))
    sw.WriteLine("machineToQCAssume[tmp] := {0};", (snd qc))
    Map.iter (fun k (v: int) -> sw.WriteLine("machineEvToQCount[tmp][{0}] := 0;", v)) evMap
    sw.WriteLine("yield;")
    sw.WriteLine("async call MachineThread_{0}(tmp, entryArg);", m)
    sw.WriteLine("m := PrtConstructFromMachineId(tmp);")
    sw.WriteLine("return;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")


  let createProbe sw name =
    fprintfn sw @"procedure %s_ProbeStateStack(event: int)
{
   if(registerEvents[CurrState][event])
   {
      return;
   }" name
   

    
    fprintfn sw "  //Probe down the state stack. 
   while(StateStack != Nil())
   {"
    fprintfn sw "      call %s_CallExitAction();" name
    fprintfn sw @"
      CurrState := state#Cons(StateStack);
      StateStack := stack#Cons(StateStack);
      if(registerEvents[CurrState][event])
      {
          return;
      }
   }"

    fprintfn sw @"   return;
}"

  let createCallEntryAction (sw: IndentedTextWriter) (name: string) (states: StateDecl list) (stateToInt: Map<string, int>) = 
    let callEntryAction (st: StateDecl) = 
      sw.WriteLine("if(state == {0}) //{1}", Map.find st.Name stateToInt, st.Name) 
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
      match st.EntryAction with
      | Some(a) -> sw.WriteLine("call {0}(payload);", a)
      | None -> sw.WriteLine()
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")

    sw.WriteLine("procedure {0}_CallEntryAction(state: int, payload: PrtRef)", name)
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    List.iter callEntryAction states
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  let createCallExitAction (sw: IndentedTextWriter) (name: string) (states: StateDecl list) (stateToInt: Map<string, int>) = 
    let callExitAction (st: StateDecl) = 
      sw.WriteLine("if(CurrState == {0}) //{1}", Map.find st.Name stateToInt, st.Name) 
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
      match st.ExitAction with
      | Some(a) -> sw.WriteLine("call {0}(null);", a)
      | None -> sw.WriteLine()
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")

    sw.WriteLine("procedure {0}_CallExitAction()", name)
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    List.iter callExitAction states
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  let translateMachine (sw: IndentedTextWriter) G evMap hasDefer hasIgnore (md: MachineDecl) =
    let stateToInt =  [for i in md.States do yield i.Name] |> Seq.mapi (fun i x -> x,i) |> Map.ofSeq
    let state = md.StateMap.[md.StartState]
    assert(not md.IsMonitor)
    (* Machine functions *)
    let funs =
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) md.Functions
      !map
    let G' = mergeMaps (mergeMaps G md.VarMap) funs

    List.iter (translateFunction sw G' stateToInt md.Name evMap) md.Functions

    if md.HasPush then createProbe sw md.Name

    createCallEntryAction sw md.Name md.States stateToInt
    createCallExitAction sw md.Name md.States stateToInt
    
    (* The actual machine thread *)
    sw.WriteLine("procedure MachineThread_{0}(mid: int, entryArg: PrtRef)", md.Name)
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("var event: int;")
    sw.WriteLine("var payload: PrtRef;")
    sw.WriteLine("var depth: int;")
    sw.WriteLine("// Initialize")
    if md.HasPush then
      sw.WriteLine("StateStack := Nil();")
    sw.WriteLine("CurrState := {0};", (Map.find md.StartState stateToInt))
    sw.WriteLine("// For raised events")
    sw.WriteLine("eventRaised := false;")
    sw.WriteLine("thisMid := mid;")
    sw.WriteLine("// Initialize machine variables.")
    md.Init |> List.iter (translateStmt sw G' stateToInt md.Name evMap)

    sw.WriteLine("// Set mappings of registered, deferred and ignored events.")

    for st in md.States do
      (getEventMaps st.Dos st.Transitions hasDefer hasIgnore evMap) |> List.iter (printEvDict sw stateToInt.[st.Name])

    match state.EntryAction with
    | Some(ea) -> sw.WriteLine("call {0}(entryArg);", ea)
    | None -> ignore true

    sw.WriteLine("while(true)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("yield;")
    sw.WriteLine("call event, payload := Dequeue();")
    if md.HasPush then sw.WriteLine("call {0}_ProbeStateStack(event);", md.Name)
    List.iter (translateState sw md stateToInt hasDefer hasIgnore evMap) md.States
    sw.WriteLine()
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("assume false;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  /// A special case for translating monitors. There's no enque/deque
  /// or deferred events or push transitions. Some statement translations will differ too.
  let createMonitor (sw: IndentedTextWriter) G evMap (md: MachineDecl) =
    let stateToInt =  [for i in md.States do yield i.Name] |> Seq.mapi (fun i x -> x,i) |> Map.ofSeq
    
    let createCallMonitorExitAction() = 
      let callExitAction (st: StateDecl) = 
        sw.WriteLine("if({0}_CurrState == {1}) //{2}", md.Name, Map.find st.Name stateToInt, st.Name) 
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        match st.ExitAction with
        | Some(a) -> sw.WriteLine("call {0}(null);", a)
        | None -> sw.WriteLine()
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")

      sw.WriteLine("procedure {0}_CallExitAction()", md.Name)
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
      List.iter callExitAction md.States
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")

    let translateMonitorTrans src (t: TransDecl.T)  =
      begin
        match t with
        | TransDecl.T.Call(e, d, f) ->
          begin
            let srcExitAction = md.StateMap.[src].ExitAction
            let dstEntryAction = md.StateMap.[d].EntryAction
            sw.WriteLine("if(event == {0}) // {1}", (Map.find e evMap), e)
            sw.WriteLine("{")
            sw.Indent <- sw.Indent + 1;
            match srcExitAction with
            | None -> ignore true
            | Some(ea) -> sw.WriteLine("call {0}(null);", ea)
            sw.WriteLine("call {0}(payload);", f)
            sw.WriteLine("{0}_CurrState := {1};", md.Name, (Map.find d stateToInt))
            match dstEntryAction with
            | None -> ignore true
            | Some(ea) -> sw.WriteLine("call {0}(payload);", ea)
            sw.Indent <- sw.Indent - 1
            sw.WriteLine("}")
          end
        | _ -> raise NotDefined
        sw.Write("else ")
      end
  
    let translateMonitorDo (d: DoDecl.T) =
      begin
        match d with
        | DoDecl.T.Ignore(e) ->
            sw.WriteLine("if(event == {0}) {{}} // {1}", (Map.find e evMap), e)
        | DoDecl.T.Call(e,f) ->
          begin
            sw.WriteLine("if(event == {0}) //{1}", (Map.find e evMap), e)
            sw.WriteLine("{")
            sw.Indent <- sw.Indent + 1
            sw.WriteLine("call {0}(payload);", f)
            sw.Indent <- sw.Indent - 1
            sw.WriteLine("}")
          end
        | _ -> raise NotDefined //No Defers.
        sw.Write("else ")
      end
    let translateMonitorState (st: StateDecl) =
      sw.WriteLine("if({0}_CurrState == {1}) // {2}", md.Name, (Map.find st.Name stateToInt), st.Name)
      sw.WriteLine("{")
      sw.WriteLine("  {0}:", st.Name)
      sw.Indent <- sw.Indent + 1
      List.iter translateMonitorDo st.Dos
      List.iter (translateMonitorTrans st.Name) st.Transitions
      let e1 = List.map (fun (t: TransDecl.T) -> match t with
                                                 | TransDecl.T.Call(e, _, _) 
                                                 | TransDecl.T.Push(e, _) -> e) st.Transitions
      let e2 = List.map (fun (t: DoDecl.T) -> match t with
                                                 | DoDecl.T.Call(e, _)
                                                 | DoDecl.T.Ignore(e) 
                                                 | DoDecl.T.Defer(e)-> e) st.Dos
      let unHandled = Set(md.MonitorList) - (Set(e1) + Set(e2))
      if unHandled.Count > 0 then begin
        sw.Write("if(")
        let conds = Set.map (fun s -> sprintf "event == %d" (Map.find s evMap)) unHandled
        let cond = String.concat " || " conds
        sw.Write(cond)
        let evNames = String.concat ", " unHandled 
        sw.WriteLine("){{}} //Nothing to do for {0}.", evNames)
        sw.Write("else")
      end
      sw.WriteLine()
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
      sw.WriteLine("assert false;") //Assume false?
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")

    let translateMonitorStmt g st =
    //Monitors may not use the 'this' keyword, perform nondeterministic choice,
    //create machines or execute send/receive.
      match st with
      | Raise(e, arg) -> 
        begin
          let plExpr = (translateExpr g evMap arg)
          let eExp = (translateEventExpr sw G evMap e plExpr)
          sw.WriteLine("call Monitor_{0}({1}, {2});", md.Name, eExp, plExpr) 
        end
      | Receive(_) -> raise NotDefined 
      | Pop -> raise NotDefined
      | Send(_) -> raise NotDefined
      | NewStmt(_) -> raise NotDefined
      | _ -> translateStmt sw g stateToInt md.Name evMap st 

    let translateMonitorFunction g (fd: FunDecl) =
      let formals = fd.Formals |> List.map (fun(v: VarDecl) -> "actual_" + v.Name + ": PrtRef") |> String.concat ", "
      let ret = if fd.RetType.IsSome then " returns (ret: PrtRef)" else ""
      sw.WriteLine("procedure {0}({1}){2}", fd.Name, formals, ret)
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
      fd.Formals |> List.map (fun(v) -> "var " + v.Name + ": PrtRef;")  |> List.iter (fun(s) -> sw.WriteLine(s))
      getVars "" fd.Locals |> List.iter (fun(x) -> sw.WriteLine("{0}", x))
      fd.Formals |> List.map (fun(v) -> v.Name + ":= actual_" + v.Name + ";") |> List.iter (fun(s) -> sw.WriteLine(s))
      
      let g' = mergeMaps g fd.VarMap
      List.iter (translateMonitorStmt g') fd.Body
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")

    createCallEntryAction sw md.Name md.States stateToInt
    createCallMonitorExitAction()
    sw.WriteLine("procedure Monitor_{0}(event: int, payload: PrtRef)", md.Name)
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    List.iter translateMonitorState md.States
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    monitorToStartState := Map.add md.Name (Map.find md.StartState stateToInt) !monitorToStartState
    let funs =
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) md.Functions
      !map
    let G' = mergeMaps (mergeMaps G md.VarMap) funs
    List.iter (translateMonitorFunction G') md.Functions

//------

  let printAssertEventCard (sw: IndentedTextWriter) evToInt (evToDecl: Map<string, EventDecl>) =
    let printEventQC e =
      sw.WriteLine("if(event == {0}) //{1}", (Map.find e evToInt), e)
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
      match (Map.find e evToDecl).QC with
      | None -> sw.WriteLine()
      | Some(Card.Assume(i)) -> sw.WriteLine("assume (count <= {0});", i)
      | Some(Card.Assert(i)) -> sw.WriteLine("assert (count <= {0});", i)
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")

    sw.WriteLine("procedure AssertEventCard(mid: int, event: int)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("var head: int;")
    sw.WriteLine("var tail: int;")
    sw.WriteLine("var count: int;")

    sw.WriteLine("head := MachineInboxHead[mid];")
    sw.WriteLine("tail := MachineInboxTail[mid];")
    sw.WriteLine("count := machineEvToQCount[mid][event];")

    sw.WriteLine("// Queue constraints for specific events.")
    Map.iter (fun k v -> (printEventQC k)) evToDecl
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  let createMonitorFunction (sw: IndentedTextWriter) evMap evToMon  =
    let printMonitorSt ev monLst =
      let e = (Map.find ev evMap)
      sw.WriteLine("if(event == {0}) //{1}", e, ev)
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
      List.iter (fun(m) -> sw.WriteLine("call Monitor_{0}({1}, payload);", m, e)) monLst
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")

    sw.WriteLine("procedure monitor(event: int, payload: PrtRef)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    Map.iter printMonitorSt evToMon
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  let createAssertPayloadDynamicType (sw: IndentedTextWriter) (evToInt: Map<string,int>) (evToDecl: Map<string, EventDecl>) =
    let printAssertion e =
      match (Map.find e evToDecl).Type with
      | None -> ignore true
      | Some(Any) -> ignore true
      | Some(t) ->
        begin
          sw.WriteLine("if(evID == {0})", (Map.find e evToInt))
          sw.WriteLine("{")
          sw.Indent <- sw.Indent + 1
          sw.WriteLine("assert PrtDynamicType(payload) == {0};", (translateType t))
          sw.Indent <- sw.Indent - 1
          sw.WriteLine("}")
        end
    sw.WriteLine("// Asserts that the payload supplied to an event variable is of the")
    sw.WriteLine("// correct type. If yes, returns the integer corresponding to the event.")
    sw.WriteLine("procedure AssertPayloadDynamicType(event: PrtRef, payload: PrtRef) returns (evID: int)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("evID := PrtFieldInt(event);")
    Map.iter (fun k v -> printAssertion k) evToInt
    sw.WriteLine("return;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  let createDeque (sw: IndentedTextWriter) hasDefer hasIgnore =    
    sw.WriteLine("procedure Dequeue() returns (event: int, payload: PrtRef)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("var ptr: int;")
    sw.WriteLine("var head: int;")
    sw.WriteLine("var tail: int;")
    sw.WriteLine("var q: int;")

    sw.WriteLine("if(eventRaised)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("eventRaised := false;")
    sw.WriteLine("event := raisedEvent;")
    sw.WriteLine("payload := raisedEventPl;")
    sw.WriteLine("return;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")


    sw.WriteLine("head := MachineInboxHead[thisMid];")
    sw.WriteLine("tail := MachineInboxTail[thisMid];")

    sw.WriteLine("ptr := head;")
    sw.WriteLine("event := 0 - 1;")

    sw.WriteLine("while(ptr <= tail)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("event := MachineInboxStoreEvent[thisMid][ptr];")
    if hasIgnore then
      begin
        sw.WriteLine("if(event >= 0 && ignoreEvents[CurrState][event])")
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        sw.WriteLine("// dequeue")
        sw.WriteLine("q := machineEvToQCount[thisMid][event];")
        sw.WriteLine("machineEvToQCount[thisMid][event] := q - 1;")
        sw.WriteLine("if(ptr == head)")
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        sw.WriteLine("MachineInboxHead[thisMid] := head + 1;")
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
        sw.WriteLine("else if(ptr == tail)")
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        sw.WriteLine("MachineInboxTail[thisMid] := tail - 1;")
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
        sw.WriteLine("else")
        sw.WriteLine("{")
        sw.Indent <- sw.Indent + 1
        sw.WriteLine("MachineInboxStoreEvent[thisMid][ptr] := 0 - 1;")
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
        sw.WriteLine("")
        sw.Indent <- sw.Indent - 1
        sw.WriteLine("}")
        sw.Write("else ")
      end
    let cond = if hasDefer then "if(event >= 0 && !deferEvents[CurrState][event])" else "if(event >= 0)"
    sw.WriteLine("{0}", cond)
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("// dequeue")
    sw.WriteLine("q := machineEvToQCount[thisMid][event];")
    sw.WriteLine("machineEvToQCount[thisMid][event] := q - 1;")
    sw.WriteLine("if(ptr == head)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("MachineInboxHead[thisMid] := head + 1;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    sw.WriteLine("else if(ptr == tail)")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("MachineInboxTail[thisMid] := tail - 1;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    sw.WriteLine("else")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("MachineInboxStoreEvent[thisMid][ptr] := 0 - 1;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    sw.WriteLine("payload := MachineInboxStorePayload[thisMid][ptr];")
    sw.WriteLine("break;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    sw.WriteLine("ptr := ptr + 1;")
    sw.WriteLine("event := 0 - 1;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

    sw.WriteLine("// block")
    sw.WriteLine("assume event >= 0;")
    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")

  let initializeMonitorGlobals (sw: IndentedTextWriter) evMap (md: MachineDecl) = 
    let funs =
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) md.Functions
      !map
    let G = mergeMaps  md.VarMap funs
    let stateToInt =  [for i in md.States do yield i.Name] |> Seq.mapi (fun i x -> x,i) |> Map.ofSeq

    List.iter (translateStmt sw G stateToInt md.Name evMap) md.Init

  let translateProg (prog: ProgramDecl) (sw: IndentedTextWriter) =
    (* Top-level types *)
    sw.WriteLine("type PrtType;")
    sw.WriteLine("const unique {0}: PrtType;", (translateType Null))
    sw.WriteLine("const unique {0}: PrtType;", (translateType Int))
    sw.WriteLine("const unique {0}: PrtType;", (translateType Bool))
    sw.WriteLine("const unique {0}: PrtType;", (translateType Machine))
    sw.WriteLine("const unique {0}: PrtType;", (translateType Type.Event))
    for i = 1 to prog.maxFields do
      sw.WriteLine("const unique PrtTypeTuple{0}: PrtType;", i)
    
    (* ref type *)
    sw.WriteLine("type PrtRef;")
    sw.WriteLine("const unique null: PrtRef;")
    sw.WriteLine("const unique PrtTrue: PrtRef;")
    sw.WriteLine("const unique PrtFalse: PrtRef;")

    (* runtime type *)
    sw.WriteLine("function PrtDynamicType(PrtRef):PrtType;")
    sw.WriteLine("")

    (* fields *)
    sw.WriteLine("function PrtIsNull(PrtRef) : bool;")
    sw.WriteLine("function PrtFieldInt(PrtRef) : int;")
    sw.WriteLine("function PrtFieldBool(PrtRef) : bool;")
    sw.WriteLine("function PrtFieldMachine(PrtRef) : int;")
    sw.WriteLine("function PrtFieldEvent(PrtRef) : int;")
    for i = 0 to (prog.maxFields-1) do
        sw.WriteLine("function PrtFieldTuple{0}(PrtRef) : PrtRef;", i)
    sw.WriteLine("function PrtFieldSeqStore(PrtRef) : [int]PrtRef;")
    sw.WriteLine("function PrtFieldSeqSize(PrtRef) : int;")
    sw.WriteLine("function PrtFieldMapKeys(PrtRef) : [int]PrtRef;")
    sw.WriteLine("function PrtFieldMapValues(PrtRef) : [int]PrtRef;")
    sw.WriteLine("function PrtFieldMapSize(PrtRef) : int;")
    sw.WriteLine("")

    (* constructors of basic types *)
    sw.WriteLine("axiom (PrtDynamicType(null) == {0});", (translateType Null))
    sw.WriteLine("axiom (PrtIsNull(null) == true);")
    sw.WriteLine("axiom (forall x : PrtRef :: {PrtIsNull(x)} x == null || !PrtIsNull(x));")
    sw.WriteLine("")
    sw.WriteLine("function PrtConstructFromInt(int) : PrtRef;")
    sw.WriteLine("axiom (forall x : int :: {PrtFieldInt(PrtConstructFromInt(x))} PrtFieldInt(PrtConstructFromInt(x)) == x);")
    sw.WriteLine("axiom (forall x : int :: {{PrtDynamicType(PrtConstructFromInt(x))}} PrtDynamicType(PrtConstructFromInt(x)) == {0});", (translateType Int))
    sw.WriteLine("")
    sw.WriteLine("function {:inline} PrtConstructFromBool(v: bool) : PrtRef")
    sw.WriteLine("{ if v then PrtTrue else PrtFalse }")
    sw.WriteLine("axiom (PrtFieldBool(PrtTrue));")
    sw.WriteLine("axiom (!PrtFieldBool(PrtFalse));")
    sw.WriteLine("axiom (PrtDynamicType(PrtTrue) == {0});", (translateType Bool))
    sw.WriteLine("axiom (PrtDynamicType(PrtFalse) == {0});", (translateType Bool))
    sw.WriteLine("")
    sw.WriteLine("function PrtConstructFromMachineId(int) : PrtRef;")
    sw.WriteLine("axiom (forall x : int :: {PrtFieldMachine(PrtConstructFromMachineId(x))} PrtFieldMachine(PrtConstructFromMachineId(x)) == x);")
    sw.WriteLine("axiom (forall x : int :: {{PrtDynamicType(PrtConstructFromMachineId(x))}} PrtDynamicType(PrtConstructFromMachineId(x)) == {0});", (translateType Machine))
    sw.WriteLine("")
    sw.WriteLine("function PrtConstructFromEventId(int) : PrtRef;")
    sw.WriteLine("axiom (forall x : int :: {PrtFieldEvent(PrtConstructFromEventId(x))} PrtFieldEvent(PrtConstructFromEventId(x)) == x);")
    sw.WriteLine("axiom (forall x : int :: {{PrtDynamicType(PrtConstructFromEventId(x))}} PrtDynamicType(PrtConstructFromEventId(x)) == {0});", (translateType Type.Event))
    sw.WriteLine("")

    (* Allocation *)
    sw.WriteLine("procedure {:allocator} AllocatePrtRef() returns (x: PrtRef);")
    sw.WriteLine("//ensures x != null;")
    sw.WriteLine("")

    (* Sequence *)
    sw.WriteLine("function {:inline} SeqIndexInBounds(seq: PrtRef, index: int) : bool")
    sw.WriteLine("{ 0 <= index && index < PrtFieldSeqSize(seq) }")
    sw.WriteLine("")
    sw.WriteLine("function {:inline} ReadSeq(seq: PrtRef, index: int) : PrtRef")
    sw.WriteLine("{ PrtFieldSeqStore(seq)[index] }")
    sw.WriteLine("")

    (* Machine Globals *)
    prog.Machines |> List.filter (fun(md: MachineDecl) -> not md.IsMonitor) |> List.map (fun(md: MachineDecl) -> md.Globals) |> List.map (getVars "{:thread_local}") |> List.fold (fun l v ->  l @ v) [] |> List.iter (fun(x)->sw.WriteLine(x))

    (* Registered, deferred, ignored events *)
    let dicts =
      ["var{:thread_local} registerEvents: [int][int]bool;"] @
      (if prog.HasIgnore then ["var{:thread_local} ignoreEvents: [int][int]bool;"] else []) @
      (if prog.HasDefer then ["var{:thread_local} deferEvents: [int][int]bool;"] else [])

    List.iter (fun(x:string) -> sw.WriteLine(x)) dicts

    (*Temp RHS vars *)
    let tmpVars = "var{:thread_local} tmpRhsValue: PrtRef;" ::[for i = 0 to prog.maxFields-1 do yield (sprintf "var{:thread_local} tmpRhsValue_%d: PrtRef;" i)] in
    tmpVars |> List.iter (fun(x) -> sw.WriteLine("{0}", x))
    
    let monitorToInt = prog.Machines |> List.filter (fun (md: MachineDecl) -> md.IsMonitor) |> List.map (fun(md: MachineDecl) -> md.Name) |> Seq.mapi (fun i x -> (x, i)) |> Map.ofSeq

    let evMap = prog.EventMap |> Map.toSeq |> Seq.map fst |> Seq.mapi (fun i x -> (x,i)) |> Map.ofSeq

    (* Create a function to send stuff to monitors*)
    createMonitorFunction sw evMap prog.EventsToMonitors 
    
    (* Create a function to assert payload type*)
    createAssertPayloadDynamicType sw evMap prog.EventMap

    (* Equals *)
    printEquals sw prog.maxFields

    (* Deque *)
    createDeque sw prog.HasDefer prog.HasIgnore

    (* Assert Event Cardinality *)
    printAssertEventCard sw evMap prog.EventMap

    let s = IO.File.ReadAllLines("CommonBpl.bpl") in
    Array.iter (fun (x:string) -> sw.WriteLine(x)) s

    let G =
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) prog.StaticFuns
      !map

    (* Static functions *)
    List.iter (translateFunction sw G Map.empty "" evMap) prog.StaticFuns

    (* Monitors *)
    let mons = List.filter (fun(m:MachineDecl) -> m.IsMonitor) prog.Machines 
    
    //Globals
    mons |> List.fold (fun acc (m: MachineDecl) -> acc @ m.Globals) [] 
    |> List.iter (fun(v: VarDecl) -> sw.WriteLine("var {0}: PrtRef;", v.Name))
    
    //Current State
    mons |> List.map (fun(md: MachineDecl) -> md.Name) 
    |> List.iter (fun(s) -> sw.WriteLine("var {0}_CurrState: int;", s))

    //Function for the monitor
    List.iter (createMonitor sw G evMap) mons

    (* New machine creation *)
    List.iter (createNewMachineFunction sw G evMap) (List.filter (fun m -> (not m.IsMonitor)) prog.Machines)

    (* Machines *)
    List.filter (fun(m: MachineDecl) -> not m.IsMonitor) prog.Machines
    |> List.iter (translateMachine sw G evMap prog.HasDefer prog.HasIgnore)

    (* Sequence and Map Types *)
    Set.iter (fun t ->
        match t with
        | Seq _ -> sw.WriteLine("const unique PrtTypeSeq{0}: PrtType; // {1}", (GetTypeIndex t), (printType t))
        | Map _ -> sw.WriteLine("const unique PrtTypeMap{0}: PrtType; // {1}", (GetTypeIndex t), (printType t))
        | _ -> ()
        ) (GetAllTypes())

    
    (* AssertIsType *)
    Set.iter (fun t -> printTypeCheck sw t) !typesAsserted

    (* The main function *)
    sw.WriteLine("procedure {:entrypoint} main()")
    sw.WriteLine("{")
    sw.Indent <- sw.Indent + 1
    sw.WriteLine("var tmpRhsValue: PrtRef;")
    sw.WriteLine("machineCounter := 0;")
    
    //Set monitor Start States.
    Map.iter (fun k v -> sw.WriteLine("{0}_CurrState := {1};", k, v)) !monitorToStartState

    //Initialize monitor globals
    mons |> List.iter (initializeMonitorGlobals sw evMap)
    
    //Start main machine
    sw.WriteLine("yield;")
    sw.WriteLine("call tmpRhsValue := newMachine_Main(null);")

    sw.Indent <- sw.Indent - 1
    sw.WriteLine("}")
    
    monitorToStartState := Map.empty
    Typmap := Map.empty
    TypmapIndex := 0
    typesAsserted := Set.empty

    0 // return an integer exit code
