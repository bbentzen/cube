(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Call-by-name prenormalization
 *       Performs full β-reduction on β-redexes of all types,
 *       η-reduction for dependent functions and paths,
 *       but not ε-reduction (i0/i1 endpoints) for dependent paths.
 **)

open Substitution

(* Returns a value and a flag determining whether there was a reduction *)

let rec has_reduction = function

  | Ast.Coe (i, j, Ast.Abs(k, Pi(x, ty1, ty2)), e) ->  
    let v1 = fresh_var (Pi(x, ty1, ty2)) e 2 in
    let c x = Ast.Coe (j, x, Ast.Abs(k, ty1), Id v1) in
    Ast.Abs(v1, Ast.Coe (i, j, Ast.Abs(k, subst x (c (Id k)) ty2), App(e, c i))), true
  
  | Ast.Coe (i, j, Ast.Abs(k, Sigma(x, ty1, ty2)), e) ->  
    let c x = Ast.Coe (i, x, Ast.Abs(k, ty1), Ast.Fst e) in
    Ast.Pair(c j, Ast.Coe (i, j, Ast.Abs(k, subst x (c (Id k)) ty2), Snd e)), true

  | Ast.Coe (i, j, Ast.Abs(k, Pathd(ty, e1, e2)), e) ->
      let v1 = fresh_var (Ast.App(e1, e2)) e 2 in
      let v2 = fresh_var (Ast.App(e1, e2)) e 3 in
      Ast.Pabs(v1, Ast.App(Ast.App (Ast.Hfill(
      Ast.Abs(v1, Ast.Coe (i, j, (Ast.Abs(k, fst (has_reduction (Ast.App(ty, Id v1))))), Ast.At(e, Ast.Id v1))), 
      Ast.Abs(v2, Coe (Id v2, j, (Ast.Abs(k, fst (has_reduction (Ast.App(ty, I0()))))), subst k (Id v2) e1)),
      Ast.Abs(v2, Coe (Id v2, j, (Ast.Abs(k, fst (has_reduction (Ast.App(ty, I1()))))), subst k (Id v2) e2))),
      I1()), Id v1)), true
  
  (* | Ast.Coe (i, j, Ast.Abs(k, Pathd(Abs(v, ty), e1, e2)), e) ->  (* Non-dependent paths *)
    if has_var k ty = false then
      let v1 = fresh_var (Ast.App(e1, e2)) e 2 in
      Ast.Pabs(v1, Ast.App(Ast.App (Ast.Hfill(
      Ast.Abs(v1, Ast.Coe (i, j, Ast.Abs(k, Abs(v, ty)), Ast.At(e, Ast.Id v1))), 
      Ast.Abs(k, Coe (Id v1, j, Ast.Abs(k, Abs(v, ty)), e1)),
      Ast.Abs(k, Coe (Id v1, j, Ast.Abs(k, Abs(v, ty)), e2))),
      I1()), Id v1)), true
    else
      let v1 = fresh_var (Ast.App(e1, e2)) e 2 in
      let v2 = fresh_var (Ast.App(e1, e2)) e 3 in
      Ast.Pabs(v1, Ast.App(Ast.App (Ast.Hfill(
      Ast.Abs(v2, Coe(Id v2, Id v1,  Abs(k, subst v (Id k) (subst k j ty)), Ast.Coe (i, j, Abs(k, subst v (Id v2) ty), Ast.At(e, Ast.Id v2)))), 
      Ast.Abs(k, Coe(I0(), Id v1,  Abs(k, subst v (Id k) (subst k j ty)), subst k j e1)),
      Ast.Abs(k, Coe(I1(), Id v1,  Abs(k, subst v (Id k) (subst k j ty)), subst k j e2))),
      I1()), Id v1)), true *)

  | Ast.Coe (i, j, e1, e2) ->
    begin
      let (i', bi) = has_reduction i in
      let (j', bj) = has_reduction j in
      let (e2', b2) = has_reduction e2 in
      if i' = j' then
        e2', true
      else
        match e1 with
        | Ast.Abs(k, e) ->
          if has_var k e then
            let (e1', b1) = has_reduction e1 in
            (* let (e2', b2) = has_reduction e2 in *)
            Ast.Coe (i', j', e1', e2'), 
            bi || bj || b1 || b2
          else
            e2', true  (* coercion regularity *)
        | _ ->
          let (e1', b1) = has_reduction e1 in
          (* let (e2', b2) = has_reduction e2 in *)
          Ast.Coe (i', j', e1', e2'), 
          bi || bj || b1 || b2
    end
  
  | Ast.Hfill (e, e1, e2) ->
    let (e', b) = has_reduction e in
    let (e1', b1) = has_reduction e1 in
    let (e2', b2) = has_reduction e2 in
    Ast.Hfill (e', e1', e2'), b || b1 || b2
  
  | Ast.App (Ast.Hfill (e, _, _), Ast.I0()) -> 
    e, true

  | Ast.App (Ast.App (Ast.Hfill (_, e1, _), i), Ast.I0()) -> 
    fst (has_reduction (Ast.App(e1, i))), true

  | Ast.App (Ast.App (Ast.Hfill (_, _, e2), i), Ast.I1()) -> 
    fst (has_reduction (Ast.App(e2, i))), true

  | Ast.Abs (x, e) -> 
    begin 
      match e with
      | Ast.App (e1 , e2) ->
        if e2 = Ast.Id x && not (has_var x e1) then 
          fst (has_reduction e1), true
        else
          let (e', b) = has_reduction e in
          Ast.Abs (x, e'), b
      | _ ->
        let (e', b) = has_reduction e in
        Ast.Abs (x, e'), b
    end

  | Ast.App (e1, e2) -> 
    begin 
      match e1 with
      | Ast.Abs (x , e) ->
        if Placeholder.has_underscore e then
          Ast.App (e1, e2), false
        else
          subst x e2 (fst (has_reduction e)), true
      | _ ->
        let (e1', b1) = has_reduction e1 in
        let (e2', b2) = has_reduction e2 in
        Ast.App (e1', e2'), b1 || b2
    end

  | Ast.Pair (e1, e2) ->
    begin
      match e1, e2 with
      | Ast.Fst e1', Ast.Snd e2' ->
        if e1' = e2' then
          e1', true
        else
          let (e1'', b1) = has_reduction e1 in
          let (e2'', b2) = has_reduction e2 in
          Ast.Pair (e1'', e2''), b1 || b2
      | _ ->
        let (e1', b1) = has_reduction e1 in
        let (e2', b2) = has_reduction e2 in
        Ast.Pair (e1', e2'), b1 || b2
    end

  | Ast.Fst e ->
    begin 
      match e with
      | Ast.Pair (e1 , _) -> (e1, true)
      | _ -> 
        let (e', b) = has_reduction e in
        Ast.Fst e', b
    end

  | Ast.Snd e -> 
    begin
      match e with
      | Ast.Pair (_ , e2) -> (e2, true)
      | _ -> 
        let (e', b) = has_reduction e in
        Ast.Snd e', b
    end

  | Ast.Inl e ->
    let (e', b) = has_reduction e in
    Ast.Inl e', b

  | Ast.Inr e -> 
    let (e', b) = has_reduction e in
    Ast.Inr e', b

  | Ast.Case (e, e1, e2) -> 
    begin
      match e with
      | Ast.Inl a -> Ast.App (e1,a), true
      | Ast.Inr b -> Ast.App (e2,b), true
      | _ ->
        let (e', b) = has_reduction e in
        let (e1', b1) = has_reduction e1 in
        let (e2', b2) = has_reduction e2 in
        Ast.Case (e', e1', e2'), b || b1 || b2
    end

  | Ast.Succ e ->
    let (e', b) = has_reduction e in
    Ast.Succ e', b

  | Ast.Natrec (e, e1, e2) -> 
    begin 
      match e with
      | Ast.Zero() -> e1, true
      | Ast.Succ k -> Ast.App (Ast.App (e2,k),Natrec(k,e1,e2)), true
      | _ -> 
        let (e', b) = has_reduction e in
        let (e1', b1) = has_reduction e1 in
        let (e2', b2) = has_reduction e2 in
        Ast.Natrec (e', e1', e2'), b || b1 || b2
    end

  | Ast.If (e, e1, e2) -> 
    begin
      match e with
      | Ast.True() -> e1, true
      | Ast.False() -> e2, true
      | _ ->
        let (e', b) = has_reduction e in
        let (e1', b1) = has_reduction e1 in
        let (e2', b2) = has_reduction e2 in
        Ast.If (e', e1', e2'), b || b1 || b2
    end

  | Ast.Let (e, e1) -> 
    begin
      match e with
      | Ast.Star() -> e1, true
      | _ -> 
        let (e', b) = has_reduction e in
        let (e1', b1) = has_reduction e1 in
        Ast.Let (e', e1'), b || b1
    end

  | Ast.Pabs (x, e) -> 
    begin 
      match e with
      | Ast.At (e1 , e2) ->
        if e2 = Ast.Id x && not (free_var x e1) then 
          fst (has_reduction e1), true
        else
          let (e', b) = has_reduction e in
          Ast.Pabs (x, e'), b
      | _ ->
        let (e', b) = has_reduction e in
        Ast.Pabs (x, e'), b
    end

  | Ast.At (e1, e2) -> 
    begin
      match e1 with
      | Ast.Pabs (x , e) ->
        if Placeholder.has_underscore e then
          Ast.At (e1, e2), false
        else
          (subst x e2 (fst (has_reduction e)), true)
      | _ ->
        let (e1', b1) = has_reduction e1 in
        let (e2', b2) = has_reduction e2 in
        Ast.At (e1', e2'), b1 || b2
    end
  
  | Ast.Pi (x, e1, e2) ->
    let (e1', b1) = has_reduction e1 in
    let (e2', b2) = has_reduction e2 in
    Ast.Pi (x, e1', e2'), b1 || b2

  | Ast.Sigma (x, e1, e2) ->
    let (e1', b1) = has_reduction e1 in
    let (e2', b2) = has_reduction e2 in
    Ast.Sigma (x, e1', e2'), b1 || b2

  | Ast.Sum (e1, e2) ->
    let (e1', b1) = has_reduction e1 in
    let (e2', b2) = has_reduction e2 in
    Ast.Sum (e1', e2'), b1 || b2

  | Ast.Pathd (e, e1, e2) -> 
    let (e', b) = has_reduction e in
    let (e1', b1) = has_reduction e1 in
    let (e2', b2) = has_reduction e2 in
    Ast.Pathd (e', e1', e2'), b || b1 || b2

  | Ast.Type l ->
    Ast.Type (Universe.eval l), false
    
  | e -> (e , false)

(* Eager prereduction: does not reduce ε-redexes *)

let reduce e = fst (has_reduction e)

(* Returns the value of an expression (may not terminate if ill-typed) *)

let rec eval e =
  let (e', b) = has_reduction e in
  if not b then e' else eval e'