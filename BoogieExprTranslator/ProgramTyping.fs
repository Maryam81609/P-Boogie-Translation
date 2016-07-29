namespace Microsoft.P2Boogie
module ProgramTyping = 
  open Syntax
  open Common
  open Helper

 (* Typing *)
  ///If not b, raise Type exception with message s.
  let typeAssert b s =
    if (not b) then 
      begin
        printfn "%s" s
        raise (TypeException s)
      end

  ///Is t1 a subtype of t2?
  let rec isSubtype t1 t2 =
    match (t1, t2) with
    | (_, Any) -> true
    | (Null, Type.Machine) -> true
    | (Null, Type.Event) -> true
    | (a,b) when a = b -> true
    | (Type.Tuple(ls1), Type.Tuple(ls2)) ->
      begin
        if List.length ls1 <> List.length ls2 then false
        else begin
          let z = List.zip ls1 ls2 in
            let z = List.map (fun (a,b) -> (isSubtype a b)) z in
              List.fold (fun p b -> p && b) true z
            end
        end
    | (Type.NamedTuple(ls1), Type.NamedTuple(ls2)) ->
      begin
        if List.length ls1 <> List.length ls2 then false
        else begin
          let z = List.zip ls1 ls2 in
              let z = List.map (fun ((f1,a),(f2,b)) -> (f1 = f2) && (isSubtype a b)) z in
                  List.fold (fun p b -> p && b) true z
              end
          end
    | _ -> false

  let rec typeof expr G =
    match expr with
    | Nil -> Null
    | ConstBool _ -> Bool
    | ConstInt _ -> Int
    | This -> Machine
    | Nondet -> Bool
    | Event _ -> Type.Event
    | Expr.Var(v) -> Map.find v G
    | Expr.Bin(Idx, e1, e2) ->
      begin
        match typeof e1 G with
        | Seq(t1) -> 
          begin
            typeAssert (isSubtype (typeof e2 G) Int) (sprintf "Type error in indexing sequence: %s" (printExpr expr))
            t1
          end
        | Map(t1, t2) ->
          begin
            typeAssert (isSubtype (typeof e2 G) t1) "Type error in indexing map"
            t2
          end
        | _ -> raise NotDefined
      end
    | Expr.Bin(In, e1, e2) ->
      begin
        match typeof e2 G with
        | Map(t1, _) ->
          begin
            typeAssert (isSubtype (typeof e1 G) t1) "Type error in key lookup"
            Bool
          end
        | _ -> raise NotDefined
      end
    | Expr.Bin(op, e1, e2) when isIntop op -> Int
    | Expr.Bin(op, e1, e2) when isBoolop op -> Bool
    | Expr.Bin(op, e1, e2) when isRelop op -> Bool
    | Expr.Bin(op, e1, e2) when isComparison op -> Bool
    | Expr.Un(Not, e1) -> Bool
    | Expr.Un(Neg, e1) -> Int
    | Expr.Un(Keys, e1) -> 
      begin
        match typeof e1 G with
        | Map(t1, t2) -> Seq(t1)
        | _ -> raise NotDefined
      end
    | Expr.Un(Values, e1) ->
      begin
        match typeof e1 G with
        | Map(t1, t2) -> Seq(t2)
        | _ -> raise NotDefined
      end
    | Expr.Un(Sizeof, e1) -> Int
    | Expr.Dot(e, i) -> 
      begin
        let ts = typeof e G in
        match ts with
        | Type.Tuple(ls) -> List.item i ls
        | _ -> raise NotDefined
      end
    | Expr.NamedDot(e, f) -> 
      begin
        let ts = typeof e G in
        match ts with
        | Type.NamedTuple(ls) -> lookupNamedFieldType f ls
        | _ -> raise NotDefined
      end
    | Cast(e, t) -> t
    | Expr.Tuple(es) -> Type.Tuple(List.map (fun e -> typeof e G) es)
    | Expr.NamedTuple(es) -> Type.NamedTuple(List.map (fun (f, e) -> (f, typeof e G)) es)
    | Default(t) -> t
    | New(_, _) -> Machine
    | Call(callee, args) -> Map.find callee G
    | _ -> raise NotDefined

  ///typeofLval <lval> <Referencing Environment>
  let rec typeofLval lval G  =
    match lval with
    | Lval.Var(v) -> Map.find v G
    | Lval.Dot(l, i) -> 
      begin
        match (typeofLval l G) with
        | Type.Tuple(ls) -> List.item i ls
        | _ -> raise NotDefined
      end
    | Lval.NamedDot(l, f) -> 
      begin
        match (typeofLval l G) with
        | Type.NamedTuple(ls) -> lookupNamedFieldType f ls
        | _ -> raise NotDefined
      end
    | Lval.Index(l, e) ->
      begin
        match typeofLval l G with
        | Type.Seq(t) -> t
        | Type.Map(t1, t2) -> t2
        | _ -> raise NotDefined
      end

  ///typecheckExpr <program> <Referencing Environment> <current machine> <expression>
  let rec typecheckExpr (prog:ProgramDecl) G cm expr =
    match expr with
    | Nil -> Null
    | ConstBool _ -> Bool
    | ConstInt _ -> Int
    | This -> Type.Machine
    | Nondet -> Bool
    | Event _ -> Type.Event
    | Expr.Var(v) -> Map.find v G
    | Expr.Bin(Idx, e1, e2) ->
      begin
        match typecheckExpr prog G cm e1 with
        | Seq(t1) -> 
          begin
            typeAssert (isSubtype (typecheckExpr prog G cm e2) Int) (sprintf "Type error in indexing sequence: %s" (printExpr expr))
            t1
          end
        | Map(t1, t2) ->
          begin
            typeAssert (isSubtype (typecheckExpr prog G cm e2) t1) "Type error in indexing map"
            t2
          end
        | _ -> raise NotDefined
      end
    | Expr.Bin(In, e1, e2) ->
      begin
        match typecheckExpr prog G cm e2 with
        | Map(t1, _) ->
          begin
            typeAssert (isSubtype (typecheckExpr prog G cm e1) t1) "Type error in key lookup"
            Bool
          end
        | _ -> raise NotDefined
      end
    | Expr.Bin(op, e1, e2) when isIntop op -> 
      begin
        typeAssert ((isSubtype (typecheckExpr prog G cm e1) Int) && (isSubtype (typecheckExpr prog G cm e2) Int)) (sprintf "Error: Non-integer arguments to intOp: %s" (printExpr expr))
        Int
      end
    | Expr.Bin(op, e1, e2) when isBoolop op -> 
      begin
        typeAssert ((isSubtype (typecheckExpr prog G cm e1) Bool) && (isSubtype (typecheckExpr prog G cm e2) Bool)) (sprintf "Error: Non-boolean arguments to boolOp: %s" (printExpr expr))
        Bool
      end
    | Expr.Bin(op, e1, e2) when isRelop op -> 
      begin
        typeAssert ((isSubtype (typecheckExpr prog G cm e1) Int) && (isSubtype (typecheckExpr prog G cm e2) Int)) (sprintf "Error: Non-integer arguments to intOp: %s" (printExpr expr))
        Bool
      end
    | Expr.Bin(op, e1, e2) when isComparison op ->
      begin
        let t1 = (typecheckExpr prog G cm e1)
        let t2 = (typecheckExpr prog G cm e2)
        typeAssert ((isSubtype t1 t2) || (isSubtype t2 t1))(sprintf "Error: Arguments to ComparisonOp not of same type: %s" (printExpr expr))
        Bool
      end
    | Expr.Un(Not, e1) -> 
      begin
        typeAssert (isSubtype (typecheckExpr prog G cm e1) Bool) 
          (sprintf "Error: Non-boolean argument to boolOp: %s" (printExpr expr))
        Bool
      end
    | Expr.Un(Neg, e1) -> 
      begin
        typeAssert (isSubtype (typecheckExpr prog G cm e1) Int) 
          (sprintf "Error: Non-integer argument to intOp: %s" (printExpr expr))
        Int
      end
    | Expr.Un(Keys, e1) -> 
      begin
        match typecheckExpr prog G cm e1 with
        | Map(t1, t2) -> Seq(t1)
        | _ -> raise NotDefined
      end
    | Expr.Un(Values, e1) ->
      begin
        match typecheckExpr prog G cm e1 with
        | Map(t1, t2) -> Seq(t2)
        | _ -> raise NotDefined
      end
    | Expr.Un(Sizeof, e1) -> 
      begin 
        match typecheckExpr prog G cm e1 with
        | Seq(_) -> Int
        | Map(_) -> Int
        | _ -> raise NotDefined
      end
    | Expr.Dot(e, i) -> 
      begin
        let ts = typecheckExpr prog G cm e in
        match ts with
        | Type.Tuple(ls) -> List.item i ls
        | _ -> raise NotDefined
      end
    | Expr.NamedDot(e, f) -> 
      begin
        let ts = typecheckExpr prog G cm e in
        match ts with
        | Type.NamedTuple(ls) -> lookupNamedFieldType f ls
        | _ -> raise NotDefined
      end
(* More checks here. Also, need to add dynamic check for down-casting. *) 
    | Cast(e, t) -> 
      let et = (typecheckExpr prog G cm e) in 
        if ((isSubtype t et) || (isSubtype et t)) then t 
        else raise (TypeException (sprintf "Cannot upcast/downcast %s to %s!" (printType et) (printType t)))
    | Expr.Tuple(es) -> Type.Tuple(List.map (fun e -> (typecheckExpr prog G cm e)) es)
    | Expr.NamedTuple(es) -> Type.NamedTuple(List.map (fun (f, e) -> (f, typecheckExpr prog G cm e)) es)
    | Default(t) -> t
    | New(m, e) -> typecheckNew prog G m e
    | Call(callee, args) -> 
      match (typecheckCall prog G cm callee args) with (* More checks here. *)
      | None -> (raise (TypeException (sprintf "A void function %s is present in expression %s" callee (printExpr expr))))
      | Some(t) -> t
    | _ -> raise NotDefined
    
  ///Checks if function call is valid; returns return type if yes.
  ///typecheckCall <program> <Referencing Environment> <current machine> <function> <args>
  and typecheckCall (prog:ProgramDecl) G cm f args = 
    let fn = 
      if (prog.FunMap.ContainsKey f) then prog.FunMap.[f]
      else (prog.MachineMap.[cm]).FunMap.[f]
    let argTypes = (List.map (fun x -> (typecheckExpr prog G cm x)) args)
    let formalTypes = (List.map (fun (x: Syntax.VarDecl) -> x.Type) fn.Formals)
    if (List.length args) <> (List.length fn.Formals) then raise NotDefined
    else
        if (not (List.fold (fun p b -> p && b) true 
                    (List.map (fun (a, b) -> (isSubtype a b)) 
                    (List.zip argTypes formalTypes)))) then
          raise (TypeException (sprintf "Non-matching types to %s: expected (%s), got (%s)" f 
                  (printList printType formalTypes ", ") 
                  (printList printType argTypes  ", ")))
        else fn.RetType
  ///Returns Type.Machine if the new is okay.
  ///typecheckNew <program> <Referencing Environment> <Machine> <expression>
  and typecheckNew (prog:ProgramDecl) G M e = 
    if (not (Map.containsKey M prog.MachineMap)) then raise NotDefined
    else begin
      let sName = (prog.MachineMap.[M]).StartState
      let ea = (prog.MachineMap.[M].StateMap.[sName]).EntryAction
      if (ea.IsSome) then begin
        if (typecheckCall prog G M ea.Value [e]).IsSome then raise NotDefined 
        else Type.Machine
      end
      else begin
        match e with
        | Expr.Nil -> Type.Machine
        | _ -> raise NotDefined
      end
    end

  ///typecheckLval <prog> <Referencing Environment> <Current Machine> <lval>
  let rec typecheckLval prog G cm lval = 
    match lval with
    | Lval.Var(v) -> Map.find v G
    | Lval.Dot(l, i) -> 
      begin
        match (typecheckLval prog G cm l) with
        | Type.Tuple(ls) -> List.item i ls
        | _ -> raise NotDefined
      end
    | Lval.NamedDot(l, f) -> 
      begin
        match (typecheckLval prog G cm l) with
        | Type.NamedTuple(ls) -> lookupNamedFieldType f ls
        | _ -> raise NotDefined
      end
    | Lval.Index(l, e) ->
      begin
        let eType = typecheckExpr prog G cm e
        match typecheckLval prog G cm l with
        | Type.Seq(t) -> 
          begin
            typeAssert (isSubtype eType Int) (sprintf "Error in indexing: %s is not an integer" (printExpr e))
            t
          end
        | Type.Map(t1, t2) ->
          begin
            typeAssert (isSubtype eType t1) (sprintf "Error in indexing: %s is not of type %s" (printExpr e) (printType t1))
            t2
          end
        | _ -> raise NotDefined
      end

  ///Check if event e with argument arg is valid to raise.
  ///typecheckCall <program> <Referencing Environment> <current machine> <event> <arg>
  let typecheckEventWithArgs (prog: Syntax.ProgramDecl) G cm event arg =
    match event with
    | Event(e) ->
      begin
        let ev = (Map.tryFind e prog.EventMap)
        typeAssert ev.IsSome (sprintf "No such event as %s!" e)
        if ev.Value.Type.IsSome then
          (typeAssert (isSubtype (typecheckExpr prog G cm arg) ev.Value.Type.Value) 
                       (sprintf "Event requires %s type %s, but got %s" e (printType ev.Value.Type.Value)
                       (printType (typecheckExpr prog G cm arg))))
        else (typeAssert (arg = Expr.Nil) (sprintf "Event %s takes no argument, but got %s" e (printExpr arg)))
      end
    | Expr.Dot(_)| Expr.NamedDot(_) | Expr.Nil | Expr.Call(_) | Expr.Default(_) | Expr.Cast(_) | Expr.Var(_) ->
      begin
        let t = typecheckExpr prog G cm event
        typeAssert (isSubtype t Type.Event) (sprintf "%s is not an event!" (printExpr event))
      end
      //ToDo add dynamic check for arg type.
    | _ -> raise NotDefined

  ///Check if a send statement is valid.
  ///typecheckSend <program> <Referencing Environment> <current machine> <destination machine> <event> <arg>
  let typecheckSend (prog: Syntax.ProgramDecl) G cm M ev arg = 
    typeAssert (isSubtype (typecheckExpr prog G cm M) Type.Machine) (sprintf "%s is not a machine!" (printExpr M))
    typecheckEventWithArgs prog G cm ev arg
 
  ///Type check statements.
  ///typecheckStmt <program> <Referencing Environment> <current machine> <current function> <statement>
  let rec typecheckStmt prog G cm cf st =
    match st with
    | Assign(l, e) -> 
      begin
        let ltype = (typecheckLval prog G cm l)
        let rtype = (typecheckExpr prog G cm e)
        typeAssert (isSubtype rtype ltype) (sprintf "Invalid assignment: %s; lhs has type %s, but rhs has type %s " (printStmt prog cm st) (printType ltype) (printType rtype))
      end
    | Insert(l, e1, e2) -> 
      match typecheckLval prog G cm l with
      | Seq(t) -> typeAssert ((isSubtype (typecheckExpr prog G cm e1) Int) && (isSubtype (typecheckExpr prog G cm e2) t)) (sprintf "Invalid insert: %s" (printStmt prog cm st))
      | Map(t1,t2) -> typeAssert ((isSubtype (typecheckExpr prog G cm e1) t1) && (isSubtype (typecheckExpr prog G cm e2) t2)) (sprintf "Invalid insert: %s" (printStmt prog cm st))
      | _ -> typeAssert false (sprintf "Invalid insert: %s" (printStmt prog cm st))
    | Remove(l, e) ->
      match typecheckLval prog G cm l with
      | Seq(t) -> typeAssert (isSubtype (typecheckExpr prog G cm e) Int) (sprintf "Invalid remove: %s" (printStmt prog cm st))
      | Map(t1,t2) -> typeAssert (isSubtype (typecheckExpr prog G cm e) t1) (sprintf "Invalid remove: %s" (printStmt prog cm st))
      | _ -> typeAssert false (sprintf "Invalid remove: %s" (printStmt prog cm st))
    | Assume e ->  typeAssert (isSubtype (typecheckExpr prog G cm e) Bool) (sprintf "Invalid assume: %s" (printStmt prog cm st))
    | Assert e -> typeAssert (isSubtype (typecheckExpr prog G cm e) Bool) (sprintf "Invalid assert: %s" (printStmt prog cm st))
    | NewStmt(m, e) -> 
      match (typecheckNew prog G m e) with
      | Type.Machine -> (typeAssert true (sprintf "Invalid New Statement: %s" (printStmt prog cm st)))
      | _ -> (typeAssert false (sprintf "Invalid New Statement: %s" (printStmt prog cm st)))
    | FunStmt(f, el, None) -> ignore (typecheckCall prog G cm f el)
    | FunStmt(f, el, v) -> 
      match (typecheckCall prog G cm f el) with
      | Some(t) -> (typeAssert (isSubtype t (Map.find v.Value G)) (sprintf "Invalid types in Statement: %s, expected type %s, but got %s" (printStmt prog cm st) (printType t) (printType (Map.find v.Value G))))
      | None -> raise NotDefined
    | Raise(e, arg) -> typecheckEventWithArgs prog G cm e arg
    | Send(M, e, arg) -> typecheckSend prog G cm M e arg
    | While(c, s) -> 
      begin 
        (typeAssert (isSubtype (typecheckExpr prog G cm c) Bool) (sprintf "%s does not have type bool!" (printExpr c)))
        (typecheckStmt prog G cm cf s)
      end
    | Ite(c, i, e) ->
      begin 
        (typeAssert (isSubtype (typecheckExpr prog G cm c) Bool) (sprintf "%s does not have type bool!" (printExpr c)))
        (typecheckStmt prog G cm cf i)
        (typecheckStmt prog G cm cf e)
      end
    | SeqStmt(lst) -> (List.iter (fun s -> (typecheckStmt prog G cm cf s)) lst)
    | Receive(lst) -> ignore true //No need because the statement list is auto-generated, and needs no typing. The actual statement block is bundled inside a function which is already type-checked.
    //ToDo add dynamic check that the event will accept the arg given.
    | Monitor(e, arg) -> (typecheckEventWithArgs prog G cm e arg)
    | Return(Some(e)) -> 
      begin
        let fn = (if (prog.FunMap.ContainsKey cf) then prog.FunMap.[cf]
                  else  (prog.MachineMap.[cm].FunMap.[cf]))
        let rettype = fn.RetType
        if (rettype.IsSome) then   
          (typeAssert (isSubtype (typecheckExpr prog G cm e) rettype.Value) 
                       (sprintf "%s: Invalid value for return expression: expected %s, got %s" cf 
                       (printType rettype.Value)
                       (printType (typecheckExpr prog G cm e))))
        else typeAssert false (sprintf "%s: Function cannot return a value, got %s" cf (printExpr e))
      end
    | Return(None) ->
      begin
        let fn = (if (prog.FunMap.ContainsKey cf) then prog.FunMap.[cf]
                  else  (prog.MachineMap.[cm].FunMap.[cf]))
        let rettype = fn.RetType
        typeAssert rettype.IsNone 
          (if rettype.IsSome then 
            (sprintf "%s: Function returns a %s, but got no return value" cf (printType rettype.Value))
          else "")
      end
    | Pop -> ignore true
    | Skip(_) -> ignore true //A fancy way of generating unit.

  let typecheckFun (prog: ProgramDecl) G cm (f: FunDecl) =
    let G' = (mergeMaps G f.VarMap)
    let body = SeqStmt(f.Body)
    (typecheckStmt prog G' cm f.Name body)
    
  let typecheckMachine (prog: ProgramDecl) G (md: MachineDecl) = 
    let funs = 
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) md.Functions
      !map 
    let G' = mergeMaps (mergeMaps G md.VarMap) funs
    (List.iter (typecheckFun prog G' md.Name) md.Functions)
    //There's no typecheckState because entry actions, exit actions,  
    //actions on transitions/dos are all functions.

  let typecheckProgram (prog: ProgramDecl) = 
    let G =           
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) prog.StaticFuns
      !map 
    (List.iter (typecheckMachine prog G) prog.Machines) 
    (List.iter (typecheckFun prog G "") prog.StaticFuns) 
