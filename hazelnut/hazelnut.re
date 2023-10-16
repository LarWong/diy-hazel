open Sexplib.Std;
open Monad_lib.Monad;
let compare_string = String.compare;
let compare_int = Int.compare;

[@deriving (sexp, compare)]
type htyp =
  | Arrow(htyp, htyp)
  | Num
  | Hole;

[@deriving (sexp, compare)]
type hexp =
  | Var(string)
  | Lam(string, hexp)
  | Ap(hexp, hexp)
  | Lit(int)
  | Plus(hexp, hexp)
  | Asc(hexp, htyp)
  | EHole
  | NEHole(hexp);

[@deriving (sexp, compare)]
type ztyp =
  | Cursor(htyp)
  | LArrow(ztyp, htyp)
  | RArrow(htyp, ztyp);

[@deriving (sexp, compare)]
type zexp =
  | Cursor(hexp)
  | Lam(string, zexp)
  | LAp(zexp, hexp)
  | RAp(hexp, zexp)
  | LPlus(zexp, hexp)
  | RPlus(hexp, zexp)
  | LAsc(zexp, htyp)
  | RAsc(hexp, ztyp)
  | NEHole(zexp);

[@deriving (sexp, compare)]
type child =
  | One
  | Two;

[@deriving (sexp, compare)]
type dir =
  | Child(child)
  | Parent;

[@deriving (sexp, compare)]
type shape =
  | Arrow
  | Num
  | Asc
  | Var(string)
  | Lam(string)
  | Ap
  | Lit(int)
  | Plus
  | NEHole;

[@deriving (sexp, compare)]
type action =
  | Move(dir)
  | Construct(shape)
  | Del
  | Finish;

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(htyp);

exception Unimplemented;

let rec erase_typ = (zt: ztyp): htyp => {
  switch (zt) {
  | Cursor(ht) => ht
  | LArrow(zt, ht) => Arrow(erase_typ(zt), ht)
  | RArrow(ht, zt) => Arrow(ht, erase_typ(zt))
  };
};

let rec erase_exp = (e: zexp): hexp => {
  switch (e) {
  | Cursor(h) => h
  | Lam(s, z) => Lam(s, erase_exp(z))
  | LAp(z, h) => Ap(erase_exp(z), h)
  | RAp(h, z) => Ap(h, erase_exp(z))
  | LPlus(z, h) => Plus(erase_exp(z), h)
  | RPlus(h, z) => Plus(h, erase_exp(z))
  | LAsc(z, ht) => Asc(erase_exp(z), ht)
  | RAsc(h, zt) => Asc(h, erase_typ(zt))
  | NEHole(z) => NEHole(erase_exp(z))
  };
};

let match_arrow = (t: htyp): option(htyp) => {
  switch (t) {
  | Num => None
  | Hole => Some(Arrow(Hole, Hole))
  | Arrow(a, b) => Some(Arrow(a, b))
  };
};

let rec is_consistent = (t: htyp, t': htyp): bool =>
  switch (t, t') {
  | (Arrow(t1, t1'), Arrow(t2, t2')) =>
    is_consistent(t1, t2) && is_consistent(t1', t2')
  | (Hole, _)
  | (_, Hole) => true
  | _ => t == t'
  };

let rec syn = (ctx: typctx, e: hexp): option(htyp) => {
  switch (e) {
  | Var(s) => TypCtx.find_opt(s, ctx)
  | Ap(e1, e2) =>
    let* t1 = syn(ctx, e1);
    let* t2 = match_arrow(t1);
    switch (t2) {
    | Arrow(t2, t) => ana(ctx, e2, t2) ? Some(t) : None
    | _ => None
    };
  | Lit(_) => Some(Num)
  | Plus(e1, e2) =>
    ana(ctx, e1, Num) && ana(ctx, e2, Num) ? Some(Num) : None
  | EHole
  | NEHole(_) => Some(Hole)
  | Asc(e, t) => ana(ctx, e, t) ? Some(t) : None
  | _ => None
  };
}

and ana = (ctx: typctx, e: hexp, t: htyp): bool => {
  switch (e) {
  | Lam(s, h) =>
    switch (match_arrow(t)) {
    | Some(Arrow(t1, t2)) => ana(TypCtx.add(s, t1, ctx), h, t2)
    | _ => false
    }
  | _ =>
    switch (syn(ctx, e)) {
    | Some(t') => is_consistent(t', t)
    | _ => false
    }
  };
};

let move_into = (e: zexp, into: zexp): option(zexp) => {
  switch (e) {
  | Lam(s, _) => Some(Lam(s, into))
  | LAp(_, h) => Some(LAp(into, h))
  | RAp(h, _) => Some(RAp(h, into))
  | LPlus(_, h) => Some(LPlus(into, h))
  | RPlus(h, _) => Some(RPlus(h, into))
  | LAsc(_, ht) => Some(LAsc(into, ht))
  | NEHole(_) => Some(NEHole(into))
  | _ => None
  };
};

let move_into_t = (e: ztyp, into: ztyp): option(ztyp) => {
  switch (e) {
  | LArrow(_, h) => Some(LArrow(into, h))
  | RArrow(h, _) => Some(RArrow(h, into))
  | _ => None
  };
};

let rec move = (e: zexp, d: dir): option(zexp) => {
  switch (d) {
  | Parent =>
    switch (e) {
    | Cursor(_) => None

    | Lam(_, z)
    | LAp(z, _)
    | RAp(_, z)
    | LPlus(z, _)
    | RPlus(_, z)
    | LAsc(z, _)
    | NEHole(z) =>
      switch (z) {
      | Cursor(_) => Some(Cursor(erase_exp(e)))
      | _ =>
        let* z1 = move(z, d);
        move_into(e, z1);
      }

    | RAsc(h, zt) =>
      switch (zt) {
      | Cursor(_) => Some(Cursor(erase_exp(e)))
      | _ =>
        let* zt' = move_type(zt, d);
        Some(RAsc(h, zt'));
      }
    }

  | Child(child) =>
    switch (e) {
    | Cursor(h) =>
      switch (h) {
      | Lam(s, h) => child == One ? Some(Lam(s, Cursor(h))) : None

      | Ap(e1, e2) =>
        child == One
          ? Some(LAp(Cursor(e1), e2)) : Some(RAp(e1, Cursor(e2)))

      | Plus(e1, e2) =>
        child == One
          ? Some(LPlus(Cursor(e1), e2)) : Some(RPlus(e1, Cursor(e2)))

      | NEHole(e) => child == One ? Some(NEHole(Cursor(e))) : None
      | Asc(h, ht) =>
        child == One
          ? Some(LAsc(Cursor(h), ht)) : Some(RAsc(h, Cursor(ht)))
      | _ => None
      }

    | Lam(_, z)
    | LAp(z, _)
    | RAp(_, z)
    | LPlus(z, _)
    | RPlus(_, z)
    | LAsc(z, _)
    | NEHole(z) =>
      let* into = move(z, d);
      move_into(e, into);

    | RAsc(h, zt) =>
      let* zt' = move_type(zt, d);
      Some(RAsc(h, zt'));
    }
  };
}
and move_type = (e: ztyp, d: dir): option(ztyp) => {
  switch (d) {
  | Parent =>
    switch (e) {
    | Cursor(_) => None

    | LArrow(z, _)
    | RArrow(_, z) =>
      switch (z) {
      | Cursor(_) => Some(Cursor(erase_typ(e)))
      | _ =>
        let* into = move_type(z, d);
        move_into_t(e, into);
      }
    }
  | Child(child) =>
    switch (e) {
    | Cursor(h) =>
      switch (h) {
      | Arrow(t1, t2) =>
        child == One
          ? Some(LArrow(Cursor(t1), t2)) : Some(RArrow(t1, Cursor(t2)))
      | _ => None
      }

    | LArrow(z, _)
    | RArrow(_, z) =>
      let* into = move_type(z, d);
      move_into_t(e, into);
    }
  };
};

let rec action_type = (t: ztyp, a: action): option(ztyp) => {
  switch (t) {
  | Cursor(t) =>
    switch (a) {
    | Construct(Arrow) => Some(RArrow(t, Cursor(Hole)))
    | Construct(Num) => t == Hole ? Some(Cursor(Num)) : None
    | Del => Some(Cursor(Hole))
    | _ => None
    }

  | LArrow(z, _)
  | RArrow(_, z) =>
    let* z' = action_type(z, a);
    switch (t) {
    | LArrow(_, h) => Some(LArrow(z', h))
    | RArrow(h, _) => Some(RArrow(h, z'))
    | _ => None
    };
  };
};

let rec syn_action =
        (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  switch (a, e) {
  | (Move(d), _) =>
    let* e' = move(e, d);
    Some((e', t));

  | (Construct(Asc), Cursor(e')) => Some((RAsc(e', Cursor(t)), t))
  | (Construct(Var(x)), Cursor(e')) =>
    let* v = TypCtx.find_opt(x, ctx);
    e' == EHole ? Some((Cursor(Var(x)), v)) : None;
  | (Construct(Lam(x)), Cursor(e')) =>
    e' == EHole
      ? Some((
          RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole)),
          Arrow(Hole, Hole),
        ))
      : None
  | (Construct(Ap), Cursor(e')) =>
    switch (match_arrow(t)) {
    | Some(Arrow(_, t2)) => Some((RAp(e', Cursor(EHole)), t2))
    | _ => Some((RAp(NEHole(e'), Cursor(EHole)), Hole))
    }
  | (Construct(Lit(n)), Cursor(e')) =>
    e' == EHole ? Some((Cursor(Lit(n)), Num)) : None
  | (Construct(Plus), Cursor(e')) =>
    is_consistent(Num, t)
      ? Some((RPlus(e', Cursor(EHole)), Num))
      : Some((RPlus(NEHole(e'), Cursor(EHole)), Num))
  | (Construct(NEHole), Cursor(e')) => Some((NEHole(Cursor(e')), Hole))
  | (Del, Cursor(_)) => Some((Cursor(EHole), Hole))

  | (Finish, Cursor(e')) =>
    switch (e') {
    | NEHole(e'') =>
      let* t' = syn(ctx, e'');
      Some((Cursor(e''), t'));
    | _ => None
    }
  | (_, Cursor(_)) => None

  | (_, LAp(z, h)) =>
    let* t2 = syn(ctx, erase_exp(z));
    let* (z', t3) = syn_action(ctx, (z, t2), a);
    let* arrow = match_arrow(t3);
    switch (arrow) {
    | Arrow(t4, t5) => ana(ctx, h, t4) ? Some((LAp(z', h), t5)) : None
    | _ => None
    };

  | (_, RAp(h, z)) =>
    let* t2 = syn(ctx, h);
    let* arrow = match_arrow(t2);
    switch (arrow) {
    | Arrow(t3, t4) =>
      let* z' = ana_action(ctx, z, a, t3);
      Some((RAp(h, z'), t4));
    | _ => None
    };
  | (_, LPlus(z, h)) =>
    let* z' = ana_action(ctx, z, a, Num);
    Some((LPlus(z', h), Num: htyp));

  | (_, RPlus(h, z)) =>
    let* z' = ana_action(ctx, z, a, Num);
    Some((RPlus(h, z'), Num: htyp));

  | (_, LAsc(z, h)) =>
    let* z' = ana_action(ctx, z, a, t);
    Some((LAsc(z', h), t));

  | (_, RAsc(h, z)) =>
    let* z' = action_type(z, a);
    ana(ctx, h, erase_typ(z'))
      ? Some((RAsc(h, z'), erase_typ(z'))) : None;

  | (_, NEHole(z)) =>
    let* t = syn(ctx, erase_exp(z));
    let* (z', _) = syn_action(ctx, (z, t), a);
    Some((NEHole(z'): zexp, Hole));
  | _ => None
  };
}

and ana_action = (ctx: typctx, z: zexp, a: action, t: htyp): option(zexp) => {
  switch (a, z) {
  | (Move(d), _) => move(z, d)

  | (Construct(Asc), Cursor(e)) => Some(RAsc(e, Cursor(t)))
  | (Construct(Lam(x)), Cursor(e)) =>
    e == EHole
      ? switch (match_arrow(t)) {
        | Some(_) => Some(Lam(x, Cursor(EHole)))
        | _ =>
          Some(NEHole(RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole))))
        }
      : None
  | (Construct(Lit(n)), Cursor(e)) =>
    e == EHole
      ? is_consistent(t, Num)
          ? Some(Cursor(Lit(n))) : Some(NEHole(Cursor(Lit(n))))
      : None
  | (Del, Cursor(_)) => Some(Cursor(EHole))
  | (Finish, Cursor(e)) =>
    switch (e) {
    | NEHole(e') => ana(ctx, e', t) ? Some(Cursor(e')) : None
    | _ => None
    }
  | (_, Cursor(e)) =>
    let* t' = syn(ctx, e);
    let* (e', t'') = syn_action(ctx, (z, t'), a);
    is_consistent(t'', t') ? Some(e') : None;

  | (_, Lam(x, e)) =>
    let* arrow = match_arrow(t);
    switch (arrow) {
    | Arrow(t1, t2) =>
      let* e' = ana_action(TypCtx.add(x, t1, ctx), e, a, t2);
      Some(Lam(x, e'): zexp);
    | _ => None
    };

  | _ =>
    let* t' = syn(ctx, erase_exp(z));
    let* (e', t'') = syn_action(ctx, (z, t'), a);
    is_consistent(t'', t) ? Some(e') : None;
  };
};