// //rule id start from : 31
// //max rule id : TODO:

// id : 45
// priority : 0
// left : data_at(?x, NULL) || data_at(NULL, ?x) at 0
// action : left_erase(0);
//          substitute(x -> NULL);

// id : 46
// priority : 0
// right : data_at(?x, NULL) || data_at(NULL, ?x) at 0
// action : right_erase(0);
//          right_add(x == NULL);

// id : 31
// priority : 0
// left : listrep(NULL) at 0
// action : left_erase(0);

// id : 32
// priority : 0
// right : listrep(NULL) at 0
// action : right_erase(0);

// id : 33
// priority : 2
// left : data_at_tail(?l, ?x) at 0
// right : data_at_tail(?y, x) at 1
// action : left_erase(0);
//          right_erase(1);
//          right_add(l == y);

// id : 43
// priority : 2
// left : listrep(?x) at 0
// right : listrep(x) at 1
// action : left_erase(0);
//          right_erase(1);

// //加入infer(x == y)后会编译失败
// /*
// id : 44
// priority : 2
// left : listrep(?x) at 0
// right : listrep(?y) at 1
// check : absense(x != y);
// action : left_erase(0);
//          right_erase(1);
// */

// /*
//  *  listrep(l) = (l == 0 && emp ) || 
//  *               exists z, l -> tail == z && listrep(z)
//  */

// id : 34
// priority : 4
// left : (?l != NULL || NULL != ?l) at 0
//        listrep(l) at 1
// action : left_erase(0);
//          left_erase(1);
//          left_exist_add(x);
//          left_exist_add(y);
//          left_add(data_at_head(l, x));
//          left_add(data_at_tail(l, y));
//          left_add(listrep(y));

// id : 35
// priority : 4
// right : (?l != NULL || NULL != ?l) at 0
//         listrep(l) at 1
// action : right_erase(0);
//          right_erase(1);
//          right_exist_add(x);
//          right_exist_add(y);
//          right_add(data_at_head(l, x));
//          right_add(data_at_tail(l, y));
//          right_add(listrep(y));

// id : 36
// priority : 4
// right : exists l, (l != NULL || NULL != l) at 0
//         listrep(l) at 1
// action : right_erase(0);
//          right_erase(1);
//          right_exist_add(x);
//          right_exist_add(y);
//          right_add(data_at_head(l, x));
//          right_add(data_at_tail(l, y));
//          right_add(listrep(y));

// id : 37
// priority : 5
// left : data_at_tail(?l, ?y) at 0
//        listrep(y) at 1
// action : left_erase(0);
//          left_erase(1);
//          left_add(listrep(l));
//          left_add(l != NULL);

// id : 38
// priority : 5
// right : data_at_tail(?l, ?y) at 0
//         listrep(y) at 1
// action : right_erase(0);
//          right_erase(1);
//          right_add(listrep(l));
//          right_add(l != NULL);

// id : 39
// priority : 5
// right : exists y, undef_data_at_tail(?l, y) at 0
//         listrep(y) at 1
// action : right_erase(0);
//          right_erase(1);
//          right_add(listrep(l));
//          right_add(l != NULL);

// id : 40
// priority : 0
// left : lseg(?x, x) at 0
// check : absense(x == NULL);
//         absense(NULL == x);
// action : left_erase(0);

// id : 41
// priority : 0
// right : lseg(?x, x) at 0
// check : absense(x == NULL);
//         absense(NULL == x);
// action : right_erase(0);

// id : 42
// priority : 0
// right : exists x, lseg(x, x) at 0
// check : absense(x == NULL);
//         absense(NULL == x);
// action : right_erase(0);

// /*
//  *   Let lseg(x, y) = x == y && emp || 
//  *                    exists z, x->tail == z && lseg(z, y)
//  */

// id : 47
// priority : 0
// left : lseg(?x, ?y) at 0
// right : lseg(x, y) at 1
// action : left_erase(0);
//          right_erase(1);

// id : 48
// priority : 4
// left : data_at(field_addr(?x, list, tail), ?y) at 0
// right : lseg(x, ?z) at 1
// action : left_erase(0);
//          right_erase(1);
//          right_exist_add(h);
//          right_add(data_at_head(x, h));
//          right_add(lseg(y, z));

// id : 49
// priority : 4
// left : data_at(field_addr(?y, list, tail), ?z) at 0
// right : lseg(?x, z) at 1
// action : left_erase(0);
//          right_erase(1);
//          right_exist_add(h);
//          right_add(data_at_head(z, h));
//          right_add(lseg(x, y));

// id : 50
// priority : 4
// left : data_at(field_addr(?y, list, tail), ?z) at 0
// right : lseg(?x, y) at 1
// action : left_erase(0);
//          right_erase(1);
//          right_exist_add(h);
//          right_add(data_at_head(y, h));
//          right_add(lseg(x, z));