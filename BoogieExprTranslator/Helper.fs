namespace Microsoft.P2Boogie

module Helper=
        
  open System
  open Syntax
  open Common
  open System.CodeDom.Compiler
     
  let mergeMaps map1 map2 = 
    (Map.fold (fun acc key value -> Map.add key value acc) map1 map2)

  (* Helpers *)
  let rec lvalToExpr lval =
    match lval with
    | Lval.Var(v) -> Expr.Var(v)
    | Lval.Dot(l, i) -> Expr.Dot(lvalToExpr l, i)
    | Lval.NamedDot(l, f) -> Expr.NamedDot(lvalToExpr l, f)
    | Lval.Index(l, e) -> Expr.Bin(Idx, lvalToExpr l, e)

  let isIntop op =
    match op with
    | Add 
    | Sub 
    | Mul 
    | Intdiv -> true
    | _ -> false

  let isRelop op =
    match op with
    | Lt 
    | Le 
    | Gt 
    | Ge -> true
    | _ -> false

  let isBoolop op =
    match op with
    | And 
    | Or -> true
    | _ -> false

  let isComparison op =
    match op with
    | Eq
    | Neq -> true
    | _ -> false

  let isSeq t =
    match t with
    | Seq _ -> true
    | _ -> false

  let isMap t =
    match t with
    | Map _ -> true
    | _ -> false

  let getDomainType t =
    match t with
    | Map(t1,t2) -> t1
    | _ -> raise NotDefined

  let getRangeType t =
    match t with
    | Map(t1, t2) -> t2
    | Seq(t2) -> t2
    | _ -> raise NotDefined

  let lookupNamedFieldType f ts =
    let (a,b) = List.find (fun (a,b) -> a = f) ts
    in b

  let lookupNamedFieldIndex f ts =
    List.findIndex (fun (a,b) -> a = f) ts
   
  (* Printing functions *)
  ///printList <printing function> <list> <seperator between elements>
  let rec printList fn ls sep=
    match ls with
    | [] -> ""
    | [h] -> (fn h)
    | h::t -> sprintf "%s%s%s" (fn h) sep (printList fn t sep)

  ///printType <type>
  let rec printType t =
    match t with
    | Null -> "null"
    | Bool -> "bool"
    | Int -> "int"
    | Machine -> "machine"
    | Type.Event -> "event"
    | Any -> "any"
    | Type.Tuple(ls) -> sprintf "(%s)" (printList printType ls ", ")
    | Type.Seq(t) -> sprintf "seq[%s]" (printType t)
    | Type.Map(t1, t2) -> sprintf "map[%s, %s]" (printType t1) (printType t2)
    | Type.NamedTuple nls -> sprintf "(%s)" (printList (fun (f,t) -> sprintf "%s: %s" f (printType t)) nls ", ")
    | Type.ModelType s -> sprintf "Model(%s)" s

  let printBinop op =
    match op with
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Intdiv -> "/"
    | And -> "&&"
    | Or -> "||"
    | Eq -> "=="
    | Neq -> "!="
    | Lt -> "<"
    | Le -> "<="
    | Gt -> ">"
    | Ge -> ">="
    | Idx -> "[]"
    | In -> "in"

  let printUop op =
    match op with
    | Not -> "!"
    | Neg -> "-"
    | Keys -> "keys"
    | Values -> "values"
    | Sizeof -> "sizeof"

  let rec printExpr (e: Expr) =
    match e with
    | Nil -> "null"
    | ConstBool(true) -> "true"
    | ConstBool(false) -> "false"
    | ConstInt(i) -> i.ToString()
    | This -> "this"
    | Nondet -> "$"
    | Event(s) -> s
    | Expr.Var(s) -> s
    | Expr.Bin(Idx, e1, e2) -> sprintf "%s[%s]" (printExpr e1) (printExpr e2) 
    | Expr.Bin(op, e1, e2) -> sprintf "(%s %s %s)" (printExpr e1) (printBinop op) (printExpr e2)
    | Expr.Un(op, e1) -> sprintf "%s(%s)" (printUop op) (printExpr e1)
    | Expr.Dot(e, i) -> (printExpr e) + "." + i.ToString()
    | Cast(e, t) -> sprintf "(%s as %s)" (printExpr e) (printType t)
    | Tuple([h]) -> sprintf "(%s,)" (printExpr h)
    | Tuple(ls) -> sprintf "(%s)" (printList printExpr ls ", ")
    | Default(t) -> sprintf "default(%s)" (printType t)
    | New(s, arg) -> sprintf "new %s(%s)" s (printExpr arg)
    | Expr.NamedDot(e,f) -> sprintf "%s.%s" (printExpr e) f
    | Expr.NamedTuple([(f, e)]) -> sprintf "(%s=%s,)"  f (printExpr e)
    | Expr.NamedTuple(es) -> sprintf "(%s)" (printList (fun (f,e) -> sprintf "%s= %s" f (printExpr e)) es ", ")
    | Expr.Call(callee, args) -> sprintf "%s(%s)" callee (printList printExpr args ", ")
   
  let rec printLval (l: Lval) =
    match l with
    | Lval.Var(v) -> v
    | Lval.Dot(v, i) -> sprintf "%s.%d" (printLval v) i
    | Lval.NamedDot(v, f) -> sprintf "%s.%s" (printLval v) f
    | Lval.Index(l, e) -> sprintf "%s[%s]" (printLval l) (printExpr e) 
  
  let openBlock (sw: IndentedTextWriter) = 
    begin
      sw.WriteLine("{")
      sw.Indent <- sw.Indent + 1
    end
  let closeBlock (sw: IndentedTextWriter) = 
    begin
      sw.Indent <- sw.Indent - 1
      sw.WriteLine("}")
    end

  let rec stmtToString prog cm s =
    match s with
    | Assign(l, e) -> sprintf "%s = %s;" (printLval l) (printExpr e)
    | Insert(l, e1, e2) -> sprintf "%s += (%s, %s);" (printLval l) (printExpr e1) (printExpr e2)
    | Remove(l, e) -> sprintf "%s -= %s;" (printLval l) (printExpr e)
    | Assert(e) -> sprintf "assert %s;" (printExpr e)
    | Assume(e) -> sprintf "assume %s;" (printExpr e)
    | NewStmt(s, Nil) -> sprintf "new %s();" s
    | NewStmt(s, e) -> sprintf "new %s(%s);" s (printExpr e)
    | Raise(e1, Nil) -> sprintf "raise %s;" (printExpr e1)
    | Raise(e1, e2) -> sprintf "raise %s, %s;" (printExpr e1) (printExpr e2)
    | Send (e1, e2, Nil) -> sprintf "send %s, %s;" (printExpr e1) (printExpr e2) 
    | Send (e1, e2, e3) -> sprintf "send %s, %s, %s;" (printExpr e1) (printExpr e2) (printExpr e3)
    | Skip(_) -> ";\n"
    | While(c, s) -> sprintf "while(%s)\n{\n%s\n}\n" (printExpr c) (stmtToString prog cm s)
    | Ite(c, i, e) -> sprintf "if(%s)\n{\n%s\n}\nelse\n{\n%s\n}\n" (printExpr c) (stmtToString prog cm i) (stmtToString prog cm e)
    | SeqStmt(l) -> sprintf "\n%s\n" (printList (stmtToString prog cm) l "\n")
    | Receive(l) -> sprintf "receive\n{\n%s\n}\n" (printList (caseToString prog cm) l "\n")
    | Pop -> "pop;"
    | Return(None) -> "return;"
    | Return(Some(e)) -> sprintf "return (%s);" (printExpr e)
    | Monitor(e1, e2) -> sprintf "monitor(%s), (%s);" (printExpr e1) (printExpr e2)
    | FunStmt(s, el, None) -> sprintf "%s(%s);" s (printList printExpr el ", ")
    | FunStmt(s, el, v) -> sprintf "%s = %s(%s);" v.Value s (printList printExpr el ", ")
    | Goto(s, e) -> sprintf "goto %s, %s" s (printExpr e)
    
  ///printEventAction <program> <event name> <machine name> <function name>
  and caseToString (prog: ProgramDecl) cm (ev, st) =     
    let evType = match (Map.find ev prog.EventMap).Type with
                 | None -> "(payload: null)"
                 | Some(t) -> sprintf "(payload: %s)" (printType t)
    sprintf "case %s: %s {\n%s\n}" ev evType (stmtToString  prog cm st)


  ///printStmt <sw> <program> <currentMachine> <stmt>
  let rec printStmt (sw: IndentedTextWriter) prog cm s =
    match s with
    | Assign(l, e) -> sw.WriteLine("{0} = {1};", (printLval l), (printExpr e))
    | Insert(l, e1, e2) -> sw.WriteLine("{0} += ({1}, {2});", (printLval l), (printExpr e1), (printExpr e2))
    | Remove(l, e) -> sw.WriteLine("{0} -= {1};", (printLval l), (printExpr e))
    | Assert(e) -> sw.WriteLine("assert {0};", (printExpr e))
    | Assume(e) -> sw.WriteLine("assume {0};", (printExpr e))
    | NewStmt(s, Nil) -> sw.WriteLine("new {0}();", s)
    | NewStmt(s, e) -> sw.WriteLine("new {0}({1});", s, (printExpr e))
    | Raise(e1, Nil) -> sw.WriteLine("raise {0};", (printExpr e1))
    | Raise(e1, e2) -> sw.WriteLine("raise {0}, {1};", (printExpr e1), (printExpr e2))
    | Send (e1, e2, Nil) -> sw.WriteLine("send {0}, {1};", (printExpr e1), (printExpr e2))
    | Send (e1, e2, e3) -> sw.WriteLine("send {0}, {1}, {2};", (printExpr e1), (printExpr e2), (printExpr e3))
    | Skip(_) -> ignore true
    | While(c, s) -> 
        begin
          sw.WriteLine("while({0})", (printExpr c))
          openBlock sw
          sw.WriteLine("{0}",(printStmt sw prog cm s))
          closeBlock sw
        end
    | Ite(c, i, e) ->
        begin
          sw.WriteLine("if({0})", (printExpr c))
          openBlock sw
          sw.WriteLine("{0}", (printStmt sw prog cm i))
          closeBlock sw
          sw.WriteLine("else")
          openBlock sw
          sw.WriteLine("{0}", (printStmt sw prog cm e))
          closeBlock sw
        end
    | SeqStmt(l) -> List.iter (printStmt sw prog cm) l
    | Receive(l) -> 
        begin
          sw.WriteLine("receive")
          openBlock sw
          List.iter (printCases sw prog cm) l
          closeBlock sw
        end
    | Pop -> sw.WriteLine("pop;")
    | Return(None) -> sw.WriteLine("return;")
    | Return(Some(e)) -> sw.WriteLine("return ({0});", (printExpr e))
    | Monitor(e1, e2) -> sw.WriteLine("monitor ({0}), ({1});", (printExpr e1), (printExpr e2))
    | FunStmt(s, el, None) -> sw.WriteLine("{0}({1});", s, (printList printExpr el ", "))
    | FunStmt(s, el, v) -> sw.WriteLine("{0} = {1}({2});", v.Value, s, (printList printExpr el ", "))
    | Goto(s, e) -> sw.WriteLine("goto {0}, {1}", s, (printExpr e))
    
  ///printCases <sw> <program> <currentMachine> <event, action>
  and printCases (sw:IndentedTextWriter) (prog: ProgramDecl) cm (ev, st) =
    let evType = match (Map.find ev prog.EventMap).Type with
                 | None -> "(payload: null)"
                 | Some(t) -> sprintf "(payload: %s)" (printType t)
    sw.Write("case {0}: {1} ", ev, evType)
    openBlock sw
    printStmt sw prog cm st
    closeBlock sw

  ///printDo <sw> <program> <DoDecl>
  let printDo (sw: IndentedTextWriter) (prog: ProgramDecl) (d: Syntax.DoDecl.T) =
    match d with
    | Syntax.DoDecl.T.Defer(s) -> sw.WriteLine("defer {0};", s)
    | Syntax.DoDecl.T.Ignore(s) -> sw.WriteLine("ignore {0};", s)
    | Syntax.DoDecl.T.Call(e, f) ->
      begin
        let evType = match (Map.find e prog.EventMap).Type with
                     | None -> "(payload: null)"
                     | Some(t) -> sprintf "(payload: %s)" (printType t)
        sw.Write("on {0} do {1} ", e, evType)
        openBlock sw
        sw.WriteLine("payload = {0}(payload);", f)
        closeBlock sw
      end

  ///printTrans <sw> <program> <DoDecl>
  let printTrans (sw: IndentedTextWriter) (prog: ProgramDecl) (t: Syntax.TransDecl.T) =
    match t with
    | Syntax.TransDecl.T.Push(e, d) -> sw.WriteLine("on {0} push {1};", e, d)
    | Syntax.TransDecl.T.Call(e, d, f) ->
      begin
        let evType = match (Map.find e prog.EventMap).Type with
                     | None -> "(payload: null)"
                     | Some(t) -> sprintf "(payload: %s)" (printType t)
        sw.Write("on {0} goto {1} with {2} ", e, d, evType)
        openBlock sw
        sw.WriteLine("{0}(payload);", f)
        closeBlock sw
      end

  let (|InvariantEqual|_|) (str:string) arg = 
    if String.Compare(str, arg, StringComparison.OrdinalIgnoreCase) = 0
      then Some() else None

  let printCard (c: Syntax.Card) =
    match c with
    | Card.Assert(i) -> sprintf " assert %i" i
    | Card.Assume(i) -> sprintf " assume %i" i

  let printVar (v: Syntax.VarDecl) = 
    sprintf "var %s: %s" v.Name (printType v.Type)
  
  let printVarList (sw: IndentedTextWriter) (ls: VarDecl list) = 
    List.iter (fun v -> sw.WriteLine("{0};", (printVar v))) ls

  ///printFunction <sw> <program> <currentMachine> <FunDecl>
  let printFunction (sw: IndentedTextWriter) prog cm (f: Syntax.FunDecl) =
    let printFormal (v: VarDecl) =
      sprintf "%s: %s" v.Name (printType v.Type)
    let model = if f.IsModel then "model " else ""
    let args = (printList printFormal f.Formals ", ")
    let ret = if (f.RetType.IsSome) then sprintf ": %s" (printType f.RetType.Value) else ""
    let body = SeqStmt(f.Body)
    sw.WriteLine("{0}fun {1}({2}){3}", model, f.Name, args, ret)
    openBlock sw
    printVarList sw f.Locals
    printStmt sw prog cm body
    closeBlock sw

  let printEvent (sw: IndentedTextWriter) (e: Syntax.EventDecl) =
    let typ = if (e.Type.IsSome) then (sprintf ": %s" (printType e.Type.Value)) else ""
    let qc = if (e.QC.IsSome) then (sprintf " %s" (printCard e.QC.Value)) else ""
    sw.WriteLine("event {0}{1}{2};", e.Name, qc, typ)

  ///printState <sw> <program> <currentMachine> <StateDecl>
  let printState (sw: IndentedTextWriter) (prog: ProgramDecl) cm (s: Syntax.StateDecl) = 
    let printEntryExit (ea: string option) action= 
      match action, ea with
      | _, None -> ignore true
      | "entry", Some(a) -> 
        begin
          let fd = if (prog.FunMap.ContainsKey a) then prog.FunMap.[a]
                   else  (prog.MachineMap.[cm].FunMap.[a]) 
          if fd.Formals.Length = 1 then begin
            sw.Write("entry (payload: {0}) ", (printType fd.Formals.Head.Type)) 
            openBlock sw
            sw.WriteLine("{0}(payload);", a)
            closeBlock sw
          end
          else
            raise NotDefined
        end
      | "exit", Some(a) -> 
        begin
          sw.Write("exit ")
          openBlock sw
          sw.WriteLine("{0}(null);", a)
          closeBlock sw
        end
      | _,_ -> raise NotDefined  

    let temp = 
      match s.Temperature with 
      | InvariantEqual "Hot" -> "hot"
      | InvariantEqual "Cold" -> "cold"
      | _ -> "" 

    sw.Write("{0} state {1} ", temp, s.Name)
    openBlock sw
    printEntryExit s.EntryAction "entry"
    printEntryExit s.ExitAction "exit"
    List.iter (printDo sw prog) s.Dos
    List.iter (printTrans sw prog) s.Transitions
    closeBlock sw

  ///printMachine <sw> <program> <MachineDecl>
  let printMachine (sw: IndentedTextWriter) (prog: ProgramDecl) (m: Syntax.MachineDecl) =
    let machine = if (m.IsModel) then "model" else (if (m.IsMonitor) then "spec" else "machine")
    let monitors = if(m.IsMonitor) then (sprintf " monitors %s " (printList (sprintf "%s") m.MonitorList ", ")) else ""
    let card = if (m.QC.IsSome) then (printCard m.QC.Value) else ""
    sw.WriteLine("{0} {1}{2}{3}", machine, m.Name, card, monitors)
    openBlock sw
    printVarList sw m.Globals
    List.iter (printFunction sw prog m.Name) m.Functions
    List.iter (fun (s: Syntax.StateDecl) -> 
                    begin
                      if (s.Name = m.StartState) then sw.Write("start ")
                      printState sw prog m.Name s
                    end)  m.States
    closeBlock sw

  let printProg (sw: IndentedTextWriter) (prog: Syntax.ProgramDecl) =
    begin
      let events = List.filter (fun(x:EventDecl) -> x.Name <> "null" && x.Name <>"halt") prog.Events
      List.iter (printEvent sw) events
      List.iter (printFunction sw prog "") prog.StaticFuns
      List.iter (printMachine sw prog) prog.Machines           
    end
 
  let tupleSize t =
    match t with
    | Type.Tuple ls -> (List.length ls)
    | _ -> 0
  
  (* find max tuple size *)
  let maxTupleSize m = 
    Map.fold (fun max t _ -> if(max < tupleSize t) then tupleSize t else max) 0 m

  (* global counter for fresh variables *)
  let globalFreshCnt = ref 0 in
  let getFreshVar () =
    begin
      let name = sprintf "Tmp%d" !globalFreshCnt in
      globalFreshCnt := !globalFreshCnt + 1
      name
    end

  let getLocal ty G =
    let name = getFreshVar() in
    (name, Map.add name ty G)
