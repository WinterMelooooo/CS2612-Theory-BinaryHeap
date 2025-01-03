id : 0
priority : 0
left: StoreExpr(?ee, ?t, ?e) at 0
right : data_at(field_addr(ee, Expr, t), ?tt) at 1
action : left_erase(0);
         right_erase(1);
         left_add(StoreExprUnion(field_addr(ee, Expr, d), tt, e));

id : 1
priority : 0
left : (?tt == 0) at 0
       StoreExprUnion(field_addr(?ee, d), tt, ?e) at 1
action : left_erase(1);
         right_add_exist(v);
         right_add(data_at(field_addr(field_addr(ee, Expr, d), u, value), int, v));
         right_add(e == ConstExpr(v));

id : 2
priority : 0
left : (?tt == 1) at 0
       StoreExprUnion(field_addr(?ee, d), tt, ?e) at 1
action : left_erase(1);
         right_add_exist(pl);
         right_add_exist(pr);
         right_add_exist(tl);
         right_add_exist(tr);
         right_add_exist(el);
         right_add_exist(er);
         right_add(data_at(field_addr(field_addr(field_addr(ee, Expr, d), u, add), ae, left), PTR, pl));
         right_add(data_at(field_addr(field_addr(field_addr(ee, Expr, d), u, add), ae, right), PTR, pr));
         right_add(StoreExpr(pl, tl, el));
         right_add(StoreExpr(pr, tr, er));
         right_add(e == AddExpr(el, er));

id : 3
priority : 0
left : (?tt == 2) at 0
       StoreExprUnion(field_addr(?ee, d), tt, ?e) at 1
action : left_erase(1);
         right_add_exist(pl);
         right_add_exist(pr);
         right_add_exist(tl);
         right_add_exist(tr);
         right_add_exist(el);
         right_add_exist(er);
         right_add(data_at(field_addr(field_addr(field_addr(ee, Expr, d), u, mul), me, left), PTR, pl));
         right_add(data_at(field_addr(field_addr(field_addr(ee, Expr, d), u, mul), me, right), PTR, pr));
         right_add(StoreExpr(pl, tl, el));
         right_add(StoreExpr(pr, tr, er));
         right_add(e == MulExpr(el, er));