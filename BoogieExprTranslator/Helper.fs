namespace Microsoft.P2Boogie

module Helper=
        
  open System
  open Syntax
  open Common
   
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
  
  let rec printStmt prog cm s =
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
    | While(c, s) -> sprintf "while(%s)\n{\n%s\n}\n" (printExpr c) (printStmt prog cm s)
    | Ite(c, i, e) -> sprintf "if(%s)\n{\n%s\n}\nelse\n{\n%s\n}\n" (printExpr c) (printStmt prog cm i) (printStmt prog cm e)
    | SeqStmt(l) -> sprintf "\n%s\n" (printList (printStmt prog cm) l "\n")
    | Receive(l) -> sprintf "receive\n{\n%s\n}\n" (printList (printCases prog cm) l "\n")
    | Pop -> "pop;"
    | Return(None) -> "return;"
    | Return(Some(e)) -> sprintf "return (%s);" (printExpr e)
    | Monitor(e1, e2) -> sprintf "monitor (%s), (%s);" (printExpr e1) (printExpr e2)
    | FunStmt(s, el, None) -> sprintf "%s(%s);" s (printList printExpr el ", ")
    | FunStmt(s, el, v) -> sprintf "%s = %s(%s);" v.Value s (printList printExpr el ", ")
    
  ///printEventAction <program> <event name> <machine name> <function name>
  and printCases (prog: ProgramDecl) cm (ev, st) =     
    let evType = match (Map.find ev prog.EventMap).Type with
                 | None -> "(payload: null)"
                 | Some(t) -> sprintf "(payload: %s)" (printType t)
    sprintf "case %s: %s {\n%s\n}" ev evType (printStmt prog cm st)

  let printDo (prog: ProgramDecl) (d: Syntax.DoDecl.T) = 
    match d with
    | Syntax.DoDecl.T.Defer(s) -> (sprintf "defer %s;" s)
    | Syntax.DoDecl.T.Ignore(s) -> (sprintf "ignore %s;" s)
    | Syntax.DoDecl.T.Call(e, f) -> 
      begin
        let evType = match (Map.find e prog.EventMap).Type with
                     | None -> "(payload: null)"
                     | Some(t) -> sprintf "(payload: %s)" (printType t)
        sprintf "on %s do %s {\n%s(payload);\n}" e evType f
      end

  let printTrans (prog: ProgramDecl) (t: Syntax.TransDecl.T) =
    match t with 
    | Syntax.TransDecl.T.Push(e, d) -> (sprintf "on %s push %s;" e d)
    | Syntax.TransDecl.T.Call(e, d, f) -> 
      begin
        let evType = match (Map.find e prog.EventMap).Type with
                     | None -> "(payload: null)"
                     | Some(t) -> sprintf "(payload: %s)" (printType t)
    
        sprintf "on %s goto %s with %s {\n%s(payload);\n}" e d evType f
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
  
  let printVarList (ls: VarDecl list) = 
    match ls with
    | [] -> ""
    | [h] -> (sprintf "%s;\n" (printVar h))
    | _ -> (sprintf "%s;\n" (printList printVar ls ";\n"))

  let printFunction prog cm (f: Syntax.FunDecl) = 
    let printFormal (v: VarDecl) = 
      sprintf "%s: %s" v.Name (printType v.Type)
    let model = if f.IsModel then "model " else ""
    let args = (printList printFormal f.Formals ", ")
    let ret = if (f.RetType.IsSome) then (sprintf ": %s" (printType f.RetType.Value)) else ""
    let locals = (printVarList f.Locals)
    let body = SeqStmt(f.Body)
    sprintf "%sfun %s(%s)%s\n{\n%s\n%s}" model f.Name args ret locals (printStmt prog cm body)

  let printEvent (e: Syntax.EventDecl) =
    let typ = if (e.Type.IsSome) then (sprintf ": %s" (printType e.Type.Value)) else ""
    let qc = if (e.QC.IsSome) then (sprintf " %s" (printCard e.QC.Value)) else ""
    sprintf "event %s%s%s" e.Name qc typ

  let printState (prog: ProgramDecl) cm (s: Syntax.StateDecl) = 
    let temp = 
      match s.Temperature with 
      | InvariantEqual "Hot" -> "hot"
      | InvariantEqual "Cold" -> "cold"
      | _ -> ""
    
    let printEntryExit (ea: string option) action= 
      match action, ea with
      | _, None -> ""
      | "entry", Some(a) -> 
        begin
          let fd = if (prog.FunMap.ContainsKey a) then prog.FunMap.[a]
                   else  (prog.MachineMap.[cm].FunMap.[a]) 
          if fd.Formals.Length = 1 then
            sprintf "entry (payload: %s) {\n%s(payload);\n}" (printType fd.Formals.Head.Type) a
          else
            raise NotDefined
        end
      | "exit", Some(a) -> sprintf "exit {\n%s(null);\n}" a
      | _,_ -> raise NotDefined   

    let entry = (printEntryExit s.EntryAction "entry")
    let exit = (printEntryExit s.ExitAction "exit")
    let dos = (printList (printDo prog) s.Dos "\n")
    let trans = (printList (printTrans prog) s.Transitions "\n")
    sprintf "\n%s state %s\n{\n%s%s%s%s}" temp s.Name entry exit dos trans

  let printMachine (prog: ProgramDecl) (m: Syntax.MachineDecl) =
    let main = if (m.Name = prog.MainMachine) then "main " else ""
    let machine = if (m.IsModel) then "model" else (if (m.IsMonitor) then "spec" else "machine")
    let monitors = if(m.IsMonitor) then (sprintf " monitors %s " (printList (sprintf "%s") m.MonitorList ", ")) else ""
    let card = if (m.QC.IsSome) then (printCard m.QC.Value) else ""
    sprintf "%s%s %s%s%s\n{\n%s\n%s%s\n}\n" main machine m.Name card monitors 
              (printVarList m.Globals) 
              (printList (printFunction prog m.Name) m.Functions "\n") 
              (printList (fun (s: Syntax.StateDecl) -> 
                            if (s.Name = m.StartState) then (sprintf "start %s" (printState prog m.Name s)) 
                            else (printState prog m.Name s))  m.States "\n")

  let printProg (prog: Syntax.ProgramDecl) (sw: System.IO.TextWriter) =
    begin
      let events = List.filter (fun(x:EventDecl) -> x.Name <> "null" && x.Name <>"halt") prog.Events
      match (printList printEvent events ";\n") with
      | "" -> sw.Write("")
      | s -> sw.WriteLine(sprintf "%s;" s)
      sw.WriteLine (printList (printFunction prog "") prog.StaticFuns "\n")
      sw.WriteLine (printList (printMachine prog) prog.Machines "\n")           
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
