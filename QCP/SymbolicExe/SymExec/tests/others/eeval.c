enum ExprType {
   ECONST, EADD, EMUL
};

struct Expr {
   enum ExprType t;
   union u {
      int value;
      struct ae { struct Expr * left_expr; struct Expr * right_expr; } add;
      struct me { struct Expr * left_expr; struct Expr * right_expr; } mul;
   }d;
};

/*@ Extern Coq (expr::*) */
/*@ Extern Coq (INT_MIN: Z)
               (INT_MAX: Z)
               (ConstExpr : Z -> expr)
               (AddExpr : expr -> expr -> expr)
               (MulExpr : expr -> expr -> expr)
               (eeval : expr -> Z)
               (StoreExpr : Z -> Z -> expr -> Assertion)
               (StoreExprUnion : Z -> Z -> expr -> Assertion)
*/

int eval(struct Expr * ee)
/*@ With e t
    Require 0 <= eeval(e) && eeval(e) < INT_MAX && StoreExpr(ee, t, e)
    Ensure  __return == eeval(e) && StoreExpr(ee, t, e)
*/
{
   switch (ee->t) {
      case ECONST: return ee->d.value;
      case EADD: return eval(ee->d.add.left_expr) + eval(ee->d.add.right_expr);
      case EMUL: return eval(ee->d.mul.left_expr) * eval(ee->d.mul.right_expr);
   }
}