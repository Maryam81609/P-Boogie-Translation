namespace Microsoft.P2Boogie

module RemoveRefParams =
  open Syntax
  open Common
  open Helper

  let idx x = 
    match x with
    | (a:int ,_,_) -> a

  let nm x =
    match x with
    | (_,b: string,_) -> b

  let typ x =
    match x with
    | (_,_,c:Type) -> c

  let rec getLvalFromExpr expr =   
    match expr with
    | Expr.Var(x) -> Lval.Var(x)
    | Expr.Dot(n, i) -> Lval.Dot((getLvalFromExpr n), i)
    | Expr.NamedDot(n, s) -> Lval.NamedDot((getLvalFromExpr n), s)
    | Expr.Bin(Idx, e1, e2) -> Lval.Index((getLvalFromExpr e1), e2)
    | _ -> raise NotDefined


  let rec removeRefParamsExpr funToRefParams funToRetType expr = 
    match expr with
    | Expr.New(n, e) -> 
      begin
        let vl, stl, e' = removeRefParamsExpr funToRefParams funToRetType e
        vl, stl, Expr.New(n, e')
      end
    | Expr.Call(f, args) -> removeRefParamsFunCall funToRefParams funToRetType true (f, args)
    | Expr.Un(op, e) ->
      begin
        let vl, stl, e' = removeRefParamsExpr funToRefParams funToRetType e
        vl, stl, Expr.Un(op, e')
      end
    | Expr.Bin(op, e1, e2) ->
      begin
        let vl1, stl1, e1' = removeRefParamsExpr funToRefParams funToRetType e1
        let vl2, stl2, e2' = removeRefParamsExpr funToRefParams funToRetType e2
        vl1 @ vl2, stl1 @ stl2, Expr.Bin(op, e1', e2')
      end
    | Expr.Dot(e, i) -> 
      begin
        let vl, stl, e' = removeRefParamsExpr funToRefParams funToRetType e
        vl, stl, Expr.Dot(e', i)
      end
    | Expr.NamedDot(e, s) -> 
      begin
        let vl, stl, e' = removeRefParamsExpr funToRefParams funToRetType e
        vl, stl, Expr.NamedDot(e', s)
      end
    | Expr.Cast(e, t) ->
      begin
        let vl, stl, e' = removeRefParamsExpr funToRefParams funToRetType e
        vl, stl, Expr.Cast(e', t)
      end
    | Expr.Tuple(ls) -> 
      begin
        let vlst, stlst, expLst = List.fold (fun (vl, stl, el) (curr_vl, curr_stl, curr_el) -> (vl @ curr_vl), (stl @ curr_stl), (el @ [curr_el])) ([],[],[]) (List.map (removeRefParamsExpr funToRefParams funToRetType) ls)
        vlst, stlst, Expr.Tuple(expLst)
      end
    | Expr.NamedTuple(ls) -> 
      begin
        let vlst, stlst, expLst = List.fold (fun (vl, stl, el) (curr_vl, curr_stl, curr_el) -> (vl @ curr_vl), (stl @ curr_stl), (el @ [curr_el])) ([],[],[]) (List.map (removeRefParamsExpr funToRefParams funToRetType) (ls |> List.map snd))
        let nmdLst = List.zip (List.map fst ls) expLst
        vlst, stlst, Expr.NamedTuple(nmdLst)
      end
    |_ -> ([], [], expr)

  and removeRefParamsFunCall funToRefParams funToRetType hasRet (f, args) = 
    match (Map.find f funToRefParams) with
    | [] -> ([], [], Call(f, args))
    | ls -> 
      begin
        let c = if hasRet then 1 else 0
        let varName = f + "_ret"
        let asgnLhs = ls |> List.map idx |> List.map (fun i -> List.item i args) |> List.map getLvalFromExpr
        let asgnRhs = ls |> Seq.mapi (fun i (x1,x2,x3) -> Expr.Dot(Expr.Var(varName), i+c)) |> List.ofSeq
        let asgns = List.zip asgnLhs asgnRhs |> List.map (fun (l,r) ->  Stmt.Assign(l,r))
        let retType = Map.find f funToRetType
        let argVl, argStl, argLst = List.fold (fun (vl, stl, el) (curr_vl, curr_stl, curr_e) -> (vl @ curr_vl), (stl @ curr_stl), (el @ [curr_e])) ([], [], [])(List.map (removeRefParamsExpr funToRefParams funToRetType) args)
        argVl @ [VarDecl(varName, retType)], 
        argStl @ [Stmt.FunStmt(f, argLst, Some(varName))] @ asgns,
        Expr.Dot(Expr.Var(varName), 0)
      end


  let rec removeRefParamsStmt funToRefParams funToRetType stmt= 
    match stmt with
    | Assign(l, e) -> 
      begin
        let vl, stl, e' = (removeRefParamsExpr funToRefParams funToRetType e)
          in vl, stl @ [Assign(l, e')]
      end
    | Insert (l, e1, e2) -> 
      begin
        let vl1, stl1, e1' = (removeRefParamsExpr funToRefParams funToRetType e1)
        let vl2, stl2, e2' = (removeRefParamsExpr funToRefParams funToRetType e2)
        vl1 @ vl2, stl1 @ stl2 @ [Insert(l, e1', e2')]
      end
    | Remove (l, e) -> 
      begin
        let vl, stl, e' = (removeRefParamsExpr funToRefParams funToRetType e)
        vl, stl @ [Remove(l, e')]
      end
    | Assume e -> 
      begin
        let vl, stl, e' = (removeRefParamsExpr funToRefParams funToRetType e)
        vl, stl @ [Assume(e')]
      end
    | Assert e -> 
      begin
        let vl, stl, e' = (removeRefParamsExpr funToRefParams funToRetType e)
        vl, stl @ [Assert(e')]
      end
    | NewStmt(s, e)->
      begin
        let vl, stl, e' = (removeRefParamsExpr funToRefParams funToRetType e)
        vl, stl @ [NewStmt(s, e')]
      end
    | Raise(e1, e2) -> 
       begin
        let vl1, stl1, e1' = (removeRefParamsExpr funToRefParams funToRetType e1)
        let vl2, stl2, e2' = (removeRefParamsExpr funToRefParams funToRetType e2)
        vl1 @ vl2, stl1 @ stl2 @ [Raise(e1', e2')]
      end
    | Send (e1, e2, e3) -> 
      begin
        let vl1, stl1, e1' = (removeRefParamsExpr funToRefParams funToRetType e1)
        let vl2, stl2, e2' = (removeRefParamsExpr funToRefParams funToRetType e2)
        let vl3, stl3, e3' = (removeRefParamsExpr funToRefParams funToRetType e3)
        vl1 @ vl2 @ vl3, stl1 @ stl2 @ stl3 @ [Send(e1', e2', e3')]
      end
    | Skip(_) -> [], [stmt]
    | While(c, s) ->
      begin
        let vlc, stlc, c' = (removeRefParamsExpr funToRefParams funToRetType c)
        let vls, stls     = (removeRefParamsStmt funToRefParams funToRetType s)
        vlc @ vls, stlc @ [While(c', SeqStmt(stls))]
      end
    | Ite(c, i, e) -> 
      begin
        let vlc, stlc, c' = (removeRefParamsExpr funToRefParams funToRetType c)
        let vli, stli     = (removeRefParamsStmt funToRefParams funToRetType i)
        let vle, stle     = (removeRefParamsStmt funToRefParams funToRetType e)
        vlc @ vli @ vle, stlc @ [Ite(c', SeqStmt(stli), SeqStmt(stle))]
      end
    | SeqStmt(l) -> 
      List.fold (fun (vl, stl) (curr_vl, curr_stl) -> (vl @ curr_vl), (stl @ curr_stl)) ([], []) (List.map (removeRefParamsStmt funToRefParams funToRetType) l)
    | Receive(l) ->
      begin
        let evs = l |> List.map fst
        let vstlst = l |> List.map snd |> List.map (removeRefParamsStmt funToRefParams funToRetType)
        let vl = vstlst |> List.map fst |> List.fold (fun acc ls -> acc @ ls) []
        let stlsts = vstlst |> List.map snd |> List.map Stmt.SeqStmt
        let recvst = List.zip evs stlsts |> Receive
        vl, [recvst]
      end
    | Pop -> [], [stmt]
    | Return(None) -> [], [stmt]
    | Return(Some(e)) -> 
      begin
        let vl, stl, e' = (removeRefParamsExpr funToRefParams funToRetType e) 
        vl, stl @ [Return(Some(e'))]
      end
    | Monitor(e1, e2) ->
      begin
        let vl1, stl1, e1' = (removeRefParamsExpr funToRefParams funToRetType e1)
        let vl2, stl2, e2' = (removeRefParamsExpr funToRefParams funToRetType e2)
        vl1 @ vl2, stl1 @ stl2 @ [Monitor(e1', e2')]
      end
    | FunStmt(f, el, v) ->
      begin
        match (Map.find f funToRefParams) with
        | [] -> [], [stmt]
        | ls -> 
          begin
            let fa = Expr.Call(f, el)
            let vl, stl, e' = (removeRefParamsFunCall funToRefParams funToRetType v.IsSome (f, el))
            vl, stl @ if v.IsSome then [Assign(Lval.Var(v.Value), e')] else []
          end
      end
  
  let removeRefParamsFunction funToRefParams funToRetType (fd: FunDecl) = 
    let vl, stl = List.fold (fun (vl, stl) (curr_vl, curr_stl) -> vl @ curr_vl, stl @ curr_stl) ([], []) (List.map (removeRefParamsStmt funToRefParams funToRetType) fd.Body)
    new FunDecl(fd.Name, fd.Formals, fd.RetType, fd.Locals @ vl, stl, fd.IsModel, fd.IsPure)

  let removeRefParamsMachine funToRefParams funToRetType (md: MachineDecl) = 
    let f' = md.Functions |> Seq.ofList |> Seq.map (fun (fd: FunDecl) -> (fd.Name, fd.RetType)) |> Map.ofSeq |>  Map.filter (fun k v -> v.IsSome) |> Map.map (fun k v -> v.Value) |> mergeMaps funToRetType
    let funs = List.map (removeRefParamsFunction funToRefParams f') md.Functions
    new MachineDecl(md.Name, md.StartState, md.Globals, funs, md.States, md.IsMonitor, md.MonitorList, md.QC, md.IsModel, md.HasPush)

  let removeRefParamsProgram funToRefParams (prog: ProgramDecl) =
    let funToRetType = prog.StaticFuns |> Seq.ofList |> Seq.map (fun (fd: FunDecl) -> (fd.Name, fd.RetType)) |> Map.ofSeq |> Map.filter (fun k v -> v.IsSome) |> Map.map (fun k v -> v.Value)
    let stfns = List.map (removeRefParamsFunction funToRefParams funToRetType) prog.StaticFuns
    let machines = List.map (removeRefParamsMachine funToRefParams funToRetType) prog.Machines
    new ProgramDecl(prog.FileName, prog.MainMachine, machines, prog.Events, prog.EventsToMonitors, stfns, prog.maxFields, prog.HasDefer, prog.HasIgnore)