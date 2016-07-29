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
  let (tmpVars: string list ref) = ref []
  let (monitorToStartState: Map<string, int> ref) = ref Map.empty

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
//    | Expr.New(_,_) -> "PrtConstructFromMachine(1)" (* TODO: Fix *)
    | Expr.Default t when t = Null || t = Machine || t = Type.Event || t = Any -> "null"
    | Expr.Default Int -> "PrtConstructFromInt(0)"
    | Expr.Default Bool -> "PrtFalse"
    | Expr.Event s -> sprintf "PrtConstructFromEvent(%d)" (Map.find s evMap)
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

  let translateMachineExpr m = 
    match m with
    | Expr.Var(x) -> sprintf "PrtFieldMachine(%s)" x
    | Expr.This   -> "thisMid"
    | _ -> raise NotDefined

  let translateEventExpr evMap e plExpr = 
    match e with
    | Expr.Var(ev) -> sprintf "AssertPayloadDynamicType(%s, %s)" ev plExpr
    | Expr.Event(ev) -> sprintf "%d" (Map.find ev evMap)
    | _ -> raise NotDefined

  let typesAsserted = ref Set.empty

  let translateAssign (sw: IndentedTextWriter) G evMap lval expr  =
    let level = ref sw.Indent
    let genRhsValue e G =
        let rhsVar = "tmpRhsValue" in
        fprintfn sw "%s := %s;" rhsVar (translateExpr G evMap e)
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
            fprintfn sw "call AssertIsType%d(%s);" (GetTypeIndex t) rhsVar
            (* the assignment *)
            fprintfn sw "%s := %s;" (getLhsVar lval) rhsVar      
        end
    | _, Expr.Tuple(es) ->
        begin
            for i = 0 to (List.length es) - 1 do
            let ei = (List.item i es) in
            fprintfn sw "tmpRhsValue_%d := %s;" i (translateExpr G evMap ei)
            fprintfn sw "call %s := AllocatePrtRef();" (getLhsVar lval)
            fprintfn sw "assume PrtDynamicType(%s) == PrtTypeTuple%d;" (getLhsVar lval) (List.length es)
            for i = 0 to (List.length es) - 1 do
            fprintfn sw "assume PrtFieldTuple%d(%s) == tmpRhsValue_%d;" i (getLhsVar lval) i
        end
    | _, Expr.Call(callee, args) ->
        begin
            fprintfn sw "call %s := %s(%s);" (getLhsVar lval) callee (printList (translateExpr G evMap) args ", ")
        end
    | _, Expr.Default(Seq(t)) ->
        begin
            fprintfn sw "call %s := AllocatePrtRef();" (getLhsVar lval)
            fprintfn sw "assume PrtDynamicType(%s) == PrtTypeSeq%d;" (getLhsVar lval) (GetTypeIndex (Seq(t)))
            fprintfn sw "assume PrtFieldSeqSize(%s) == 0;" (getLhsVar lval) 
        end
    | _, Expr.Default(Map(t1, t2)) ->
        begin
            fprintfn sw "call %s := AllocatePrtRef();" (getLhsVar lval)
            fprintfn sw "assume PrtDynamicType(%s) == PrtTypeMap%d;" (getLhsVar lval) (GetTypeIndex (Map(t1, t2)))
            fprintfn sw "assume PrtFieldMapSize(%s) == 0;" (getLhsVar lval) 
        end
    | _, Expr.Bin(Idx, e1, e2) ->
        begin
            match isMap (typeof e1 G) with
            | true ->  fprintfn sw "call %s := ReadMap(%s, %s);" (getLhsVar lval) (translateExpr G evMap e1) (translateExpr G evMap e2)
            | false -> fprintfn sw "assert SeqIndexInBounds(%s, PrtFieldInt(%s)); %s := ReadSeq(%s, PrtFieldInt(%s));" (translateExpr G evMap e1) (translateExpr G evMap e2) (getLhsVar lval) (translateExpr G evMap e1) (translateExpr G evMap e2)
        end
    | _, Expr.Bin(In, e1, e2) ->
        begin
            fprintfn sw "call %s := MapContainsKey(%s, %s);" (getLhsVar lval) (translateExpr G evMap e1) (translateExpr G evMap e2)
        end
    | _, Expr.Bin(Eq, e1, e2) ->
        begin
            fprintfn sw "call %s := PrtEquals(%s, %s);" (getLhsVar lval) (translateExpr G evMap e1) (translateExpr G evMap e2)
        end
    | _, Expr.Un(Keys, e) ->
        begin
            fprintfn sw "call %s := MapGetKeys(%s);" (getLhsVar lval) (translateExpr G evMap e)
        end
    | _, Expr.Un(Values, e) ->
        begin
            fprintfn sw "call %s := MapGetValues(%s);" (getLhsVar lval) (translateExpr G evMap e)
        end
    | _, Expr.Nondet ->
        begin
            fprintfn sw "havoc %s;" (getLhsVar lval) 
        end
    | Lval.Var(v), Expr.New(m, arg) ->
      begin
        fprintfn sw "machineCounter := machineCounter + 1;"
        fprintfn sw "async call MachineThread_%s(machineCounter, %s);" m (translateExpr G evMap arg)
        fprintfn sw "%s := PrtConstructFromMachineId(machineCounter);" v
      end   
    | Lval.Index(Lval.Var(lhsVar), e), _ when isSeq (typeofLval (Lval.Var(lhsVar)) G) ->
        begin
            fprintfn sw "call %s := WriteSeq(%s, PrtFieldInt(%s), %s);" lhsVar lhsVar (translateExpr G evMap e) (translateExpr G evMap expr)
        end
    | Lval.Index(Lval.Var(lhsVar), e), _ ->
        begin
            fprintfn sw "call %s := WriteMap%s, %s, %s);" lhsVar lhsVar (translateExpr G evMap e) (translateExpr G evMap expr)
        end
    | _, _ ->
        fprintfn sw "%s := %s;" (getLhsVar lval) (translateExpr G evMap expr)

  let translateInsert sw G evMap v e1 e2 =
    match isSeq (typeof (Expr.Var(v)) G) with
    | true -> fprintfn sw "call %s := InsertSeq(%s, PrtFieldInt(%s), %s);" v v (translateExpr G evMap e1) (translateExpr G evMap e2)
    | false -> fprintfn sw "call %s := InsertMap(%s, PrtFieldInt(%s), %s);" v v (translateExpr G evMap e1) (translateExpr G evMap e2)

  let translateRemove sw G evMap v e1 =
    match isSeq (typeof (Expr.Var(v)) G) with
    | true -> fprintfn sw "call %s := RemoveSeq(%s, PrtFieldInt(%s));" v v (translateExpr G evMap e1)
    | false -> fprintfn sw "call %s := RemoveMap(%s, PrtFieldInt(%s));" v v (translateExpr G evMap e1)

  let rec translateStmt (sw: IndentedTextWriter) G evMap stmt =
    let level = ref sw.Indent
    let translateCase (e, st) =
      fprintfn sw "if(event == %d)" (Map.find e evMap)
      fprintfn sw "{"
      level := !level + 1
      translateStmt sw G evMap st
      level := !level - 1
      fprintfn sw "}"
      fprintfn sw "else "
    match stmt with
    | Assign(l, e) -> translateAssign sw G evMap l e
    | Insert(Lval.Var(v), e1, e2) -> translateInsert sw G evMap v e1 e2
    | Remove(Lval.Var(v), e1) -> translateRemove sw G evMap v e1
    | Assume(e) -> fprintfn sw "assume PrtFieldBool(%s);" (translateExpr G evMap e)
    | Assert(e) -> fprintfn sw "assert PrtFieldBool(%s);" (translateExpr G evMap e)
    | NewStmt(m, e) -> fprintfn sw "call tmpRhsValue := newMachine_%s(%s)" m (translateExpr G evMap e)     
    | Raise(e, a) ->
      begin
        let plExpr = (translateExpr G evMap a)
        fprintfn sw "eventRaised := true;"
        fprintfn sw "raisedEvent := %s;" (translateEventExpr evMap e plExpr)
        fprintfn sw "raisedEventPl := %s;" plExpr
      end
    | Send(m, e, arg) ->
      begin
        let plExpr = (translateExpr G evMap arg)
      fprintfn sw "call send(%s, %s, %s);" (translateMachineExpr m) (translateEventExpr evMap e plExpr) plExpr
      end
    | Skip(_,-1,_) -> ignore true
    | Skip(f, l, c) -> fprintfn sw "assume {:sourceloc \"%s\", %d, %d} true;" f l c
    | While(c, st) ->
      begin
        fprintfn sw "while(PrtFieldBool(%s))" (translateExpr G evMap c)
        fprintfn sw "{"
        level := !level + 1
        translateStmt sw G evMap st
        level := !level - 1
        fprintfn sw "}"
      end
    | Ite(c, i, e) ->
      begin
        fprintfn sw "if(PrtFieldBool(%s))" (translateExpr G evMap c)
        fprintfn sw "{"
        level := !level + 1
        translateStmt sw G evMap i
        level := !level - 1
        fprintfn sw "}"
        fprintfn sw "else"
        fprintfn sw "{"
        level := !level + 1
        translateStmt sw G evMap e
        level := !level - 1
        fprintfn sw "}"     
      end
    | SeqStmt(ls) -> List.iter (translateStmt sw G evMap) ls
    | Receive(ls) -> 
      begin
        fprintfn sw "call event, payload := Dequeue();"
        List.iter translateCase ls
        fprintfn sw ""
        fprintfn sw "{"
        level := !level + 1
        fprintfn sw "assert false;"
        level := !level - 1
        fprintfn sw "}"
      end
    | Pop -> fprintfn sw "call StateStackPop();"
    | Return(None) -> fprintfn sw "return;"
    | Return(Some(e)) -> 
      begin
        fprintfn sw "ret := %s" (translateExpr G evMap e)
        fprintfn sw "return;"
      end
    | Monitor(e, arg) ->
      begin
        let plExpr = (translateExpr G evMap arg)
        fprintfn sw "monitor(%s,  %s);" (translateEventExpr evMap e plExpr) plExpr
      end
    | FunStmt(f, el, v) ->
      begin
        let args = el |> List.map (translateExpr G evMap) |> String.concat ", "
        let lhs = match v with 
                  | None -> ""
                  | Some(x) -> sprintf " %s := " x
        fprintfn sw "call %s%s(%s);" lhs f args
      end
    | _ -> raise NotDefined

  let fprintfnComment sw x = 
    fprintf sw "// "
    fprintfn sw x

  let printEquals sw maxFields =
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
        fprintfn sw "  if(ta == PrtTypeTuple%d) { call v := PrtEqualsTuple%d(a,b); return; }" i i
    
    fprintfn sw "
    // Map, Seq type
    assume false;
  }        
    "
    for i = 1 to maxFields do
      fprintfn sw "procedure PrtEqualsTuple%d(x: PrtRef, y: PrtRef) returns (v: PrtRef) {" i
      for j = 0 to (i-1) do
      fprintfn sw "  call v := PrtEquals(PrtFieldTuple%d(x), PrtFieldTuple%d(y));" j j
      if j <> (i-1) then fprintfn sw "  if(v == PrtFalse) { return; }"
      fprintfn sw "}"
 
  let printTypeCheck sw t =
    let tindex =  GetTypeIndex t  in
    fprintfn sw "// Type %s" (printType t)
    fprintfn sw "procedure AssertIsType%d(x: PrtRef) {" tindex
    match t with
    | Null -> raise NotDefined
    | Any -> raise NotDefined
    | Bool 
    | Seq(_)
    | Map(_, _)
    | Int -> fprintfn sw "  assert PrtDynamicType(x) == %s;" (translateType t)
    | Machine
    | Type.Event -> fprintfn sw "  assert PrtDynamicType(x) == %s || PrtIsNull(x);" (translateType t)
    | Type.NamedTuple(_) -> raise NotDefined
    | Type.ModelType s -> fprintfn sw "  assert PrtDynamicType(x) == PrtTypeModel%s;" s
    | Type.Tuple ts ->
    begin
        fprintfn sw "  assert PrtDynamicType(x) == PrtTypeTuple%d;" (List.length ts)
        for i = 0 to ((List.length ts) - 1) do
        let ti = List.item i ts in
        fprintfn sw "  call AssertIsType%d(PrtFieldTuple%d(x));" (GetTypeIndex ti) i
    end
    fprintfn sw "}"   
  
  let getVars attr (vdList: VarDecl list) =
    List.map (fun(vd: VarDecl) -> sprintf "var%s %s: PrtRef; // %s" attr vd.Name (printType vd.Type)) vdList
    
  let getDefaults (vdList: VarDecl list) = 
    List.fold (fun ls (vd: VarDecl) -> ls @ [Stmt.Assign(Lval.Var(vd.Name), Expr.Default(vd.Type))]) [] vdList 

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
  
  let printEvDict sw (state: int) (evDict, name)= 
    Map.iter (fun k v ->(fprintfn sw "%s[%d][%d] := %b;" name state k v)) evDict 

  let translateFunction (sw: IndentedTextWriter) G evMap (fd: FunDecl) = 
    let level = ref sw.Indent
    let formals = fd.Formals |> List.map (fun(v: VarDecl) -> v.Name + ": PrtRef") |> String.concat ", "
    let ret = if fd.RetType.IsSome then " returns (ret: PrtRef)" else ""
    fprintfn sw "procedure %s(%s)%s" fd.Name formals ret
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "// Initialize locals."
    getVars "" fd.Locals |> List.iter (fprintfn sw "%s")
    !tmpVars |> List.iter (fprintfn sw "%s")
    getDefaults fd.Locals |> List.iter (translateStmt sw G evMap)
    List.iter (translateStmt sw G evMap) fd.Body
    level := !level - 1
    fprintfn sw "}"
  
  let translateDos (sw: IndentedTextWriter) events (d: DoDecl.T) =
    let level = ref sw.Indent
    match d with 
    | DoDecl.T.Call(e, f) -> 
      begin
        fprintfn sw "    if(event == %d) //%s" (Map.find e events) e
        fprintfn sw "    {"
        level := !level + 1
        fprintfn sw "       call %s(payload);" f
        level := !level - 1
        fprintfn sw "    }"
      end
    | DoDecl.T.Ignore(e) ->  fprintfn sw "    if(event == %d) {} //%s" (Map.find e events) e

  let translateTransitions (sw: IndentedTextWriter) (mach: MachineDecl) src stateToInt events (t: TransDecl.T) =
    let level = ref sw.Indent
    match t with 
    | TransDecl.T.Call(e, d, f) -> 
      begin
        let srcExitAction = mach.StateMap.[src].ExitAction
        let dstEntryAction = mach.StateMap.[d].EntryAction
        fprintfn sw "    if(event == %d) // %s" (Map.find e events) e
        fprintfn sw "    {"
        level := !level + 1;  
        match srcExitAction with
        | None -> ignore true
        | Some(ea) -> fprintfn sw "       call %s();" ea
        fprintfn sw "       call %s(payload);" f
        fprintfn sw "       CurrState := %d;" (Map.find d stateToInt)
        match dstEntryAction with
        | None -> ignore true
        | Some(ea) -> fprintfn sw "       call %s(payload);" ea   
        level := !level - 1
        fprintfn sw "    }"
        fprintf sw "else "
      end
    |TransDecl.T.Push(e, d) ->  
      begin
        let dstEntryAction = mach.StateMap.[d].EntryAction
        fprintfn sw "    if(event == %d) // %s" (Map.find e events) e
        fprintfn sw "    {"
        level := !level + 1
        fprintfn sw "       call StateStackPush(%d);" (Map.find src stateToInt)
        fprintfn sw "       CurrState := %d;" (Map.find d stateToInt)
        match dstEntryAction with
        | None -> ignore true
        | Some(ea) -> fprintfn sw "       call %s(payload);" ea   
        level := !level - 1
        fprintfn sw "    }"
        fprintf sw "else "
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

  let translateState (sw: IndentedTextWriter) mach stateToInt hasDefer hasIgnore events (state: StateDecl) =
    let level = ref sw.Indent
    fprintfn sw "   if(CurrState == %d)" (Map.find state.Name stateToInt)
    fprintfn sw "   {"
    level := !level + 1
    List.iter (translateDos sw events) state.Dos
    List.iter (translateTransitions sw mach state.Name stateToInt events) state.Transitions
    if (not (haltHandled state)) then
      begin
        fprintfn sw "      if(event == %d) //halt" (Map.find "halt" events)
        fprintfn sw "      {"
        level := !level + 1
        fprintfn sw "         return;"
        level := !level - 1
        fprintfn sw "      }"
        fprintfn sw "      else" 
      end
    //Raise exception for unhandled event.
    fprintfn sw ""
    fprintfn sw "      {"
    level := !level + 1
    fprintfn sw "          assert false;" //ToDo Assert or assume?
    level := !level - 1
    fprintfn sw "      }"
    level := !level - 1
    fprintfn sw "    }"
    fprintf sw "   else "

  let createNewMachineFunction (sw: IndentedTextWriter) G evMap (md: MachineDecl) = 
    let level = ref sw.Indent
    let m = md.Name
    fprintfn sw "procedure newMachine_%s(entryArg: PrtRef) returns (m: PrtRef)" m
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "machineCounter := machineCounter + 1;"
    fprintfn sw "call InitializeInbox(machineCounter);"
    fprintfn sw "// For raised events"
    fprintfn sw "eventRaised := false;"
    fprintfn sw "// Generate Queue Constraint Mappings"
    let qc = 
      match md.QC with
      | Some(Card.Assert(i)) -> sprintf "%d" i, "0 - 1"
      | Some(Card.Assume(i)) -> "0 - 1", sprintf "%d" i
      | None -> "0 - 1", "0 - 1"
    fprintfn sw "machineToQCAssert[machineCounter] := %s;" (fst qc)
    fprintfn sw "machineToQCAssume[machineCounter] := %s;" (snd qc)
    Map.iter (fun k v -> (fprintfn sw "machineEvToQCount[machineCounter][%d] := 0;" v)) evMap
    fprintfn sw "async call MachineThread_%s(machineCounter, entryArg);" m
    fprintfn sw "m := PrtConstructFromMachineId(machineCounter);"
    fprintfn sw "return;"
    level := !level - 1
    fprintfn sw "}"

  let translateMachine (sw: IndentedTextWriter) G evMap hasDefer hasIgnore (md: MachineDecl) =
    let level = ref sw.Indent
    let stateToInt =  [for i in md.States do yield i.Name] |> Seq.mapi (fun i x -> x,i) |> Map.ofSeq
    let state = md.StateMap.[md.StartState]
    
    (* Machine functions *)
    let funs = 
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) md.Functions
      !map 
    let G' = mergeMaps (mergeMaps G md.VarMap) funs
    
    List.iter (translateFunction sw G evMap) md.Functions

    (* The actual machine thread *)
    fprintfn sw "procedure MachineThread_%s(mid: int, entryArg: PrtRef)" md.Name
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "   var event: int;"
    fprintfn sw "   var payload: PrtRef;"
    fprintfn sw "   // Initialize"
    if md.HasPush then
      fprintfn sw "   StateStack := Nil();"
    fprintfn sw "   CurrState := %d;" (Map.find md.StartState stateToInt)
    fprintfn sw "   thisMid := mid;"
    fprintfn sw "   // Initialize machine variables."
    md.Globals |> getDefaults |> List.iter (translateStmt sw G evMap)
    
    fprintfn sw "  // Set mappings of registered, deferred and ignored events."
    
    for st in md.States do
      (getEventMaps st.Dos st.Transitions hasDefer hasIgnore evMap) |> List.iter (printEvDict sw stateToInt.[st.Name])

    match state.EntryAction with
    | Some(ea) -> fprintfn sw "   call %s(entryArg);" ea
    | None -> ignore true

    fprintfn sw "   while(true)"
    fprintfn sw "   {"
    level := !level + 1
    fprintfn sw "      call event, payload := Dequeue();"
    List.iter (translateState sw md stateToInt hasDefer hasIgnore evMap) md.States
    fprintfn sw ""
    fprintfn sw "      {"
    level := !level + 1
    fprintfn sw "         assume false;"
    level := !level - 1
    fprintfn sw "      }"
    level := !level - 1
    fprintfn sw "   }"
    level := !level - 1
    fprintfn sw "}"
  
  /// A special case for translating monitors. There's no enque/deque
  /// or deferred events or push transitions. Some statement translations will differ too.
  let createMonitor (sw: IndentedTextWriter) G evMap (md: MachineDecl) = 
    let level = ref sw.Indent
    let stateToInt =  [for i in md.States do yield i.Name] |> Seq.mapi (fun i x -> x,i) |> Map.ofSeq
    
    let translateMonitorTrans src (t: TransDecl.T)  =
      match t with
      | TransDecl.T.Call(e, d, f) -> 
        begin 
          let srcExitAction = md.StateMap.[src].ExitAction
          let dstEntryAction = md.StateMap.[d].EntryAction
          fprintfn sw "    if(event == %d) // %s" (Map.find e evMap) e
          fprintfn sw "    {"
          level := !level + 1;  
          match srcExitAction with
          | None -> ignore true
          | Some(ea) -> fprintfn sw "       call %s();" ea
          fprintfn sw "       call %s(payload);" f
          fprintfn sw "       %s_CurrState := %d;" md.Name (Map.find d stateToInt) 
          match dstEntryAction with
          | None -> ignore true
          | Some(ea) -> fprintfn sw "       call %s(payload);" ea   
          level := !level - 1
          fprintfn sw "    }"
          fprintf sw "else "
        end
      | _ -> raise NotDefined
    let translateMonitorDo (d: DoDecl.T) = 
      match d with
      | DoDecl.T.Ignore(e) -> 
          fprintfn sw "    if(event == %d) {} // %s " (Map.find e evMap) e
      | _ -> raise NotDefined

    let translateMonitorState (st: StateDecl) =  
      fprintfn sw "if(%s_CurrState == %d) // %s" md.Name (Map.find st.Name stateToInt) st.Name
      fprintfn sw "{"
      level := !level + 1  
      List.iter translateMonitorDo st.Dos
      List.iter (translateMonitorTrans st.Name) st.Transitions
      level := !level - 1
      fprintfn sw "}"

    let translateMonitorStmt st = 

    let translateMonitorFunction (fd: FunDecl) = 
      let formals = fd.Formals |> List.map (fun(v: VarDecl) -> v.Name + ": PrtRef") |> String.concat ", "
      let ret = if fd.RetType.IsSome then " returns (ret: PrtRef)" else ""
      fprintfn sw "procedure %s(%s)%s" fd.Name formals ret
      fprintfn sw "{"
      level := !level + 1
      fprintfn sw "// Initialize locals."
      getVars "" fd.Locals |> List.iter (fprintfn sw "%s")
      !tmpVars |> List.iter (fprintfn sw "%s")
      getDefaults fd.Locals |> List.iter (translateStmt sw G evMap)
      List.iter translateMonitorStmt fd.Body
      level := !level - 1
      fprintfn sw "}"

    
    fprintfn sw "procedure Monitor_%s(event: int, payload: PrtRef)" md.Name
    fprintfn sw "{"
    level := !level + 1
    List.iter translateMonitorState md.States
    level := !level - 1
    fprintfn sw "}"
    monitorToStartState := Map.add md.Name (Map.find md.StartState stateToInt) 
      !monitorToStartState
    
    
    






  let printAssertEventCard (sw: IndentedTextWriter) evToInt (evToDecl: Map<string, EventDecl>) = 
    let level = ref sw.Indent
    let printEventQC e = 
      match (Map.find e evToDecl).QC with
      | None -> ignore true
      | Some(Card.Assume(i)) ->
        begin
          fprintfn sw "if(event == %d) //%s" (Map.find e evToInt) e
          fprintfn sw "{"
          level := !level + 1
          fprintfn sw "assume (count <= %d);" i
          level := !level - 1
          fprintfn sw "}"
        end
      | Some(Card.Assert(i)) -> 
        begin
          fprintfn sw "if(event == %d) //%s" (Map.find e evToInt) e
          fprintfn sw "{"
          level := !level + 1
          fprintfn sw "assert (count <= %d);" i
          level := !level - 1
          fprintfn sw "}"
        end

    fprintfn sw  "procedure AssertEventCard(mid: int, event: int)"
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "var head: int;"
    fprintfn sw "var tail: int;"
    fprintfn sw "var count: int;"
   
    fprintfn sw "head := MachineInboxHead[mid];"
    fprintfn sw "tail := MachineInboxTail[mid];"
    fprintfn sw "count := machineEvToQCount[mid][event];"
    
    fprintfn sw "//Queue constraints for specific events."
    Map.iter (fun k v -> (printEventQC k)) evToDecl
    level := !level - 1
    fprintfn sw "}"
   
  let createMonitorFunction (sw: IndentedTextWriter) evMap evToMon monToInt = 
    let level = ref sw.Indent
    let printMonitorSt ev monLst = 
      let e = (Map.find ev evMap)
      fprintfn sw "if(event == %d) //%s" e ev
      fprintfn sw "{"
      level := !level + 1
      List.iter (fun(m) -> fprintfn sw "Enqueue(%d, %d, payload);" (Map.find m monToInt) e) monLst
      level := !level - 1
      fprintfn sw "}"
    fprintfn sw "procedure monitor(event: int, payload: PrtRef)"
    fprintfn sw "{"
    level := !level + 1
    Map.iter printMonitorSt evToMon
    level := !level - 1
    fprintfn sw "}"
  
  let createAssertPayloadDynamicType (sw: IndentedTextWriter) evToInt (evToDecl: Map<string, EventDecl>) = 
    let level = ref sw.Indent
    let printAssertion e =  
      match (Map.find e evToDecl).Type with
      | None -> ignore true
      | Some(Any) -> ignore true
      | Some(t) -> 
        begin
          fprintfn sw "if(evID == %d)" (Map.find e evToInt)
          fprintfn sw "{"
          level := !level + 1
          fprintfn sw "assert PrtDynamicType(payload) == %s;" (translateType t)
          level := !level - 1
          fprintfn sw "}"
        end
    fprintfn sw "// Asserts that the payload supplied to an event variable is of the"
    fprintfn sw "// correct type. If yes, returns the integer corresponding to the event."
    fprintfn sw "procedure AssertPayloadDynamicType(event: PrtRef, payload: PrtRef) returns (evID: int)"
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "evID := PrtFieldInt(event);"
    Map.iter (fun k v -> printAssertion k) evToInt
    fprintfn sw "return;"
    level := !level - 1
    fprintfn sw "}"

  let createDeque (sw: IndentedTextWriter) hasDefer hasIgnore = 
    let level = ref sw.Indent
    fprintfn sw "procedure Dequeue() returns (event: int, payload: PrtRef)"
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "var ptr: int;"
    fprintfn sw "var head: int;"
    fprintfn sw "var tail: int;"
    fprintfn sw "var q: int;"
    
    fprintfn sw "if(eventRaised)"
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "eventRaised := false;"
    fprintfn sw "event := raisedEvent;"
    fprintfn sw "payload := raisedEventPl;"
    fprintfn sw "return;"
    level := !level - 1
    fprintfn sw "}"


    fprintfn sw "head := MachineInboxHead[thisMid];"
    fprintfn sw "tail := MachineInboxTail[thisMid];"

    fprintfn sw "ptr := head;"
    fprintfn sw "event := 0 - 1;"

    fprintfn sw "while(ptr <= tail) "
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "event := MachineInboxStoreEvent[thisMid][ptr];"
    if hasIgnore then
      begin 
        fprintfn sw "if(event >= 0 && ignoreEvents[event]) "
        fprintfn sw "{"
        level := !level + 1
        fprintfn sw "// dequeue"
        fprintfn sw "q := machineEvToQCount[thisMid][event];"
        fprintfn sw "machineEvToQCount[thisMid][event] := q - 1;"
        fprintfn sw "if(ptr == head)"
        fprintfn sw "{"
        level := !level + 1
        fprintfn sw "MachineInboxHead[thisMid] := head + 1;"
        level := !level - 1
        fprintfn sw "}"
        fprintfn sw "else if(ptr == tail) "
        fprintfn sw "{"
        level := !level + 1
        fprintfn sw "MachineInboxTail[thisMid] := tail - 1;"
        level := !level - 1
        fprintfn sw "}"
        fprintfn sw "else"
        fprintfn sw "{"
        level := !level + 1
        fprintfn sw "MachineInboxStoreEvent[thisMid][ptr] := 0 - 1;"
        level := !level - 1
        fprintfn sw "}"
        fprintfn sw ""
        level := !level - 1
        fprintfn sw "}"
        fprintf sw "else "
      end
    let cond = if hasDefer then "if(event >= 0 && !deferEvents[event])" else "if(event >= 0)"
    fprintfn sw "%s" cond
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "// dequeue"
    fprintfn sw "q := machineEvToQCount[thisMid][event];"
    fprintfn sw "machineEvToQCount[thisMid][event] := q - 1;"
    fprintfn sw "if(ptr == head)"
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "MachineInboxHead[thisMid] := head + 1;"
    level := !level - 1
    fprintfn sw "}"
    fprintfn sw "else if(ptr == tail) "
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "MachineInboxTail[thisMid] := tail - 1;"
    level := !level - 1
    fprintfn sw "}"
    fprintfn sw "else"
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "MachineInboxStoreEvent[thisMid][ptr] := 0 - 1;"
    level := !level - 1
    fprintfn sw "}"
    fprintfn sw "payload := MachineInboxStorePayload[thisMid][ptr];"
    fprintfn sw "break;"
    level := !level - 1
    fprintfn sw "}"
    fprintfn sw "ptr := ptr + 1;"
    fprintfn sw "event := 0 - 1;"
    level := !level - 1
    fprintfn sw "}"

    fprintfn sw "// block"
    fprintfn sw "assume event >= 0;"
    level := !level - 1
    fprintfn sw "}"

  let translateProg (prog: ProgramDecl) (sw: IndentedTextWriter) = 
    let level = ref sw.Indent
  (* Top-level types *)
    fprintfn sw "type PrtType;";
    fprintfn sw "const unique %s: PrtType;" (translateType Null)
    fprintfn sw "const unique %s: PrtType;" (translateType Int)
    fprintfn sw "const unique %s: PrtType;" (translateType Bool)
    fprintfn sw "const unique %s: PrtType;" (translateType Machine)
    fprintfn sw "const unique %s: PrtType;" (translateType Type.Event)
    for i = 1 to prog.maxFields do
        fprintfn sw "const unique PrtTypeTuple%d: PrtType;" i
    Set.iter (fun t -> 
        match t with
        | Seq _ -> fprintfn sw "const unique PrtTypeSeq%d: PrtType; // %s" (GetTypeIndex t) (printType t)
        | Map _ -> fprintfn sw "const unique PrtTypeMap%d: PrtType; // %s" (GetTypeIndex t) (printType t)
        | _ -> ()
        ) (GetAllTypes())
  
    (* ref type *)
    fprintfn sw "type PrtRef;"
    fprintfn sw "const unique null: PrtRef;"
    fprintfn sw "const unique PrtTrue: PrtRef;"
    fprintfn sw "const unique PrtFalse: PrtRef;"

    (* runtime type *)
    fprintfn sw "function PrtDynamicType(PrtRef):PrtType;"
    fprintfn sw ""

    (* fields *)
    fprintfn sw "function PrtIsNull(PrtRef) : bool;" 
    fprintfn sw "function PrtFieldInt(PrtRef) : int;" 
    fprintfn sw "function PrtFieldBool(PrtRef) : bool;" 
    fprintfn sw "function PrtFieldMachine(PrtRef) : int;" 
    fprintfn sw "function PrtFieldEvent(PrtRef) : int;" 
    for i = 0 to (prog.maxFields-1) do 
        fprintfn sw "function PrtFieldTuple%d(PrtRef) : PrtRef;" i 
    fprintfn sw "function PrtFieldSeqStore(PrtRef) : [int]PrtRef;" 
    fprintfn sw "function PrtFieldSeqSize(PrtRef) : int;" 
    fprintfn sw "function PrtFieldMapKeys(PrtRef) : [int]PrtRef;" 
    fprintfn sw "function PrtFieldMapValues(PrtRef) : [int]PrtRef;" 
    fprintfn sw "function PrtFieldMapSize(PrtRef) : int;" 
    fprintfn sw "" 

    (* constructors of basic types *)
    fprintfn sw "axiom (PrtDynamicType(null) == %s);" (translateType Null)
    fprintfn sw "axiom (PrtIsNull(null) == true);" 
    fprintfn sw "axiom (forall x : PrtRef :: {PrtIsNull(x)} x == null || !PrtIsNull(x));"
    fprintfn sw ""
    fprintfn sw "function PrtConstructFromInt(int) : PrtRef;" 
    fprintfn sw "axiom (forall x : int :: {PrtFieldInt(PrtConstructFromInt(x))} PrtFieldInt(PrtConstructFromInt(x)) == x);" 
    fprintfn sw "axiom (forall x : int :: {PrtDynamicType(PrtConstructFromInt(x))} PrtDynamicType(PrtConstructFromInt(x)) == %s);" (translateType Int)
    fprintfn sw ""
    fprintfn sw "function {:inline} PrtConstructFromBool(v: bool) : PrtRef"
    fprintfn sw "{ if v then PrtTrue else PrtFalse }"
    fprintfn sw "axiom (PrtFieldBool(PrtTrue));"
    fprintfn sw "axiom (!PrtFieldBool(PrtFalse));"
    fprintfn sw "axiom (PrtDynamicType(PrtTrue) == %s);" (translateType Bool)
    fprintfn sw "axiom (PrtDynamicType(PrtFalse) == %s);" (translateType Bool)
    fprintfn sw ""
    fprintfn sw "function PrtConstructFromMachineId(int) : PrtRef;" 
    fprintfn sw "axiom (forall x : int :: {PrtFieldMachine(PrtConstructFromMachineId(x))} PrtFieldMachine(PrtConstructFromMachineId(x)) == x);" 
    fprintfn sw "axiom (forall x : int :: {PrtDynamicType(PrtConstructFromMachineId(x))} PrtDynamicType(PrtConstructFromMachineId(x)) == %s);" (translateType Machine)
    fprintfn sw ""
    fprintfn sw "function PrtConstructFromEventId(int) : PrtRef;" 
    fprintfn sw "axiom (forall x : int :: {PrtFieldEvent(PrtConstructFromEventId(x))} PrtFieldEvent(PrtConstructFromEventId(x)) == x);" 
    fprintfn sw "axiom (forall x : int :: {PrtDynamicType(PrtConstructFromEventId(x))} PrtDynamicType(PrtConstructFromEventId(x)) == %s);" (translateType Type.Event)
    fprintfn sw ""


    (* Allocation *)
    fprintfn sw "procedure {:allocator} AllocatePrtRef() returns (x: PrtRef);"
    fprintfn sw "  //ensures x != null;"
    fprintfn sw ""

    (* Sequence *)
    fprintfn sw "function {:inline} SeqIndexInBounds(seq: PrtRef, index: int) : bool"
    fprintfn sw "{ 0 <= index && index < PrtFieldSeqSize(seq) }"
    fprintfn sw ""
    fprintfn sw "function {:inline} ReadSeq(seq: PrtRef, index: int) : PrtRef"
    fprintfn sw "{ PrtFieldSeqStore(seq)[index] }"
    fprintfn sw ""

    (* Machine Globals *)
    prog.Machines |> List.filter (fun(md: MachineDecl) -> not md.IsMonitor) |> List.map (fun(md: MachineDecl) -> md.Globals) |> List.map (getVars "{:thread_local}") |> List.fold (fun l v ->  l @ v) [] |> List.iter (fprintfn sw "%s")

    (* Registered events *)
    
    (* deferred, ignored events *)
    let dicts = 
      ["var{:thread_local} registerEvents: [int][int]bool;"] @ 
      (if prog.HasIgnore then ["var{:thread_local} ignoreEvents: [int]bool;"] else []) @
      (if prog.HasDefer then ["var{:thread_local} deferEvents: [int]bool;"] else [])

    List.iter (fprintfn sw "%s") dicts

    (*Temp RHS vars *)
    tmpVars := "var tmpRhsValue: PrtRef;" ::
    [for i = 0 to prog.maxFields-1 do yield (sprintf "var tmpRhsValue_%d: PrtRef;" i)]
        
    let monitorToInt = prog.Machines |> List.filter (fun (md: MachineDecl) -> md.IsMonitor) |> List.map (fun(md: MachineDecl) -> md.Name) |> Seq.mapi (fun i x -> (x, i)) |> Map.ofSeq
    
    let evMap = prog.EventMap |> Map.toSeq |> Seq.map fst |> Seq.mapi (fun i x -> (x,i)) |> Map.ofSeq
    
    createMonitorFunction sw evMap prog.EventsToMonitors monitorToInt
    createAssertPayloadDynamicType sw evMap prog.EventMap

    (* Equals *)
    printEquals sw prog.maxFields
    
    (* AssertIsType *)
    Set.iter (fun t -> printTypeCheck sw t) !typesAsserted
    
    (* Deque *)
    createDeque sw prog.HasDefer prog.HasIgnore

    let s = IO.File.ReadAllLines("CommonBpl.bpl") in
    Array.iter (fun s -> fprintfn sw "%s" s) s
      
    let G =           
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) prog.StaticFuns
      !map 
    
    (* Static functions *)
    List.iter (translateFunction sw G evMap) prog.StaticFuns
    
    (* Monitors *)    


    
    (* New machine creation *)
    List.iter (createNewMachineFunction sw G evMap) prog.Machines

    (* Machines *)
    List.filter (fun(m: MachineDecl) -> not m.IsMonitor) prog.Machines  
    |> List.iter (translateMachine sw G evMap prog.HasDefer prog.HasIgnore)

    (* The main function *)
    
    fprintfn sw "procedure {:entrypoint} main()" 
    fprintfn sw "{"
    level := !level + 1
    fprintfn sw "var tmpRhsValue: PrtRef;"
    fprintfn sw "machineCounter := 0;"
    //Start monitors 
    Map.iter (fun k v -> (fprintfn sw "call tmpRhsValue := newMachine_%s(null);" k)) monitorToInt
    
    //Start main machine
    
    fprintfn sw "call tmpRhsValue := newMachine_%s(null);" prog.MainMachine

    level := !level - 1
    fprintfn sw "}"
    
    0 // return an integer exit code
