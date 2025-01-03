//test curent rules
//max rule id:30

id : 0
priority : 0
left : (?x == x) at 0
action : left_erase(0);

id : 1
priority : 0
right : (?x == x) at 0
action : right_erase(0);

id : 2
priority : 0
left :   atom x,
         (x == null) || (null == x) at 0
action : left_erase(0);
         substitute(x -> null);

id : 3
priority : 1
right : exists x, (x == ?y) || (?y == x) at 0
action : right_erase(0);
         instantiate(x -> y);

id : 4
priority : 0
left : sll{?A}(?storeA, null, ?l) at 0
action : left_erase(0);
         left_add(l == nil{A});
 
id : 5
priority : 0
right : sll{?A}(?storeA, null, ?l) at 0
action : right_erase(0);
         right_add(l == nil{A});

id : 6
priority : 2
left : data_at(?p, ?x) at 0
right : data_at(p, ?y) at 1
action : left_erase(0);
         right_erase(1);
         right_add(x == y);

id : 7
priority : 2
left : sll{?A}(?storeA,?p, ?l0) at 0
right : sll{A}(storeA, p, ?l1) at 1
action : left_erase(0);
         right_erase(1);
         right_add(l0 == l1);

id : 8
priority : 4
left : sll{?A}(?storeA, ?p, ?l) at 0
       (p != NULL || NULL != p) at 1
action : left_erase(0);
         left_exist_add(x);
         left_exist_add(l0);
         left_add(sll{A}(storeA, p, cons{A}(x, l0)));
         left_add(l == cons{A}(x, l0));
 
id : 9
priority : 4
left : (?p != NULL || NULL != ?p) at 0
right : sll{?A}(?storeA, p, ?l) at 1
action : right_erase(1);
         right_exist_add(x);
         right_exist_add(l0);
         right_add(sll{A}(storeA, p, cons{A}(x, l0)));
         right_add(l == cons{A}(x, l0));
 
 
id : 10
priority : 3
left : sll{?A}(?storeA, p, cons{A}(x, l)) at 0
action : left_erase(0);
         left_exist_add(y);
         left_exist_add(h);
         left_add(data_at(field_addr(p, list, head), PTR(list), h));
         left_add(storeA(h, x));
         left_add(data_at(field_addr(p, list, next), PTR(list), y));
         left_add(sll{A}(storeA, y, l));
 
id : 11
priority : 3
right : sll{?A}(?storeA, p, cons{A}(x, l)) at 0
action : right_erase(0);
         right_exist_add(y);
         right_exist_add(h);
         right_add(data_at(field_addr(p, list, head), PTR(list), h));
         right_add(storeA(h, x));
         right_add(data_at(field_addr(p, list, next), PTR(list), y));
         right_add(sll{A}(storeA, y, l));
 
id : 12
priority : 3
left : sllseg{A}(?storeA, ?p, ?q, ?l0) at 0
right : sll{A}(storeA, p, ?l1) at 1
action : left_erase(0);
         right_erase(1);
         right_exist_add(l2);
         right_add(l1 == append{A}(l0, l2));
         right_add(sll{A}(storeA, q, l2));
 
id : 13
priority : 0
left : data_at(?p, ?x) at 0
check : absense(p != NULL);
        absense(NULL != p);
action : left_add(p != NULL);
 
 
id : 14
priority : 0
left : atom p, storeA(p, ?x) || data_at(field_addr(p, list, next), ?y) at 0
check : absense(p != NULL);
        absense(NULL != p);
action : left_add(p != NULL);


id : 15
priority : 0
left : storeA(?p, ?x) at 0
right : exists y, storeA(p, y) at 1
action : left_erase(0);
         right_erase(1);
         instantiate(y -> x);

id : 16
priority : 0
left : storeA(?p, ?x) at 0
right : storeA(p, ?y) at 1
action : left_erase(0);
         right_erase(1);
         right_add(x == y);

id : 17
priority : 0
left : sllseg{A}(?storeA, ?p, p, ?l) at 0
check : absense(l == nil{A});
        absense(nil{A} == l);
action : left_erase(0);
         left_add(l == nil{A});

id : 18
priority : 0
right : sllseg{A}(?storeA, ?p, p, ?l) at 0
check : absense(l == nil{A});
        absense(nil{A} == l);
action : right_erase(0);
         right_add(l == nil{A});

// id : 17
// priority : 0
// left : data_at(field_addr(?p, list, head), ?x) at 0
// right : data_at_head(p, x) at 1
// action : left_erase(0);
//          right_erase(1);

// id : 26
// priority : 0
// left : data_at(field_addr(?p, list, head), ?x) at 0
// right : exists y, data_at_head(p, y) at 1
// action : left_erase(0);
//          right_erase(1);
//          instantiate(y -> x);

// id : 18
// priority : 0
// left : data_at_tail(?p, ?x) at 0
// right : data_at(field_addr(p, list, tail), x) at 1
// action : left_erase(0);
//          right_erase(1);

// id : 19
// priority : 0
// left : data_at_tail(?p, ?x) at 0
// right : exists y, data_at(field_addr(p, list, tail), y) at 1
// action : left_erase(0);
//          right_erase(1);
//          instantiate(y -> x);

// id : 20
// priority : 0
// left : data_at(field_addr(?p, list, tail), ?x) at 0
// right : data_at_tail(p, x) at 1
// action : left_erase(0);
//          right_erase(1);

// id : 27
// priority : 0
// left : data_at(field_addr(?p, list, tail), ?x) at 0
// right : exists y, data_at_tail(p, y) at 1
// action : left_erase(0);
//          right_erase(1);
//          instantiate(y -> x);

// //risk strategy: 21, 22
// id : 21
// priority : 3
// left : sllseg(?x, x, ?l) at 0
// check : absense(x == NULL);
//         absense(NULL == x);
// action : left_erase(0);
//          right_add(l == nil);

// id : 22
// priority : 3
// right : sllseg(?x, x, ?l) at 0
// check : absense(x == NULL);
//         absense(NULL == x);
// action : right_erase(0);
//          right_add(l == nil);

// id : 23
// priority : 1
// right : exists l, sllseg(?x, x, l) at 0
// check : absense(x == NULL);
//         absense(NULL == x);
// action : right_erase(0);
//          instantiate(l -> nil);

// id : 24
// priority : 3
// left : sllseg(?x, ?y, ?l) at 0
// right : sllseg(x, ?z, ?l0) at 1
// action : left_erase(0);
//          right_erase(1);
//          right_exist_add(l1);
//          right_add(sllseg(y, z, l1));
//          right_add(l0 == app(l, l1));

// id : 25
// priority : 3
// left : sllseg(?x, ?y, ?l) at 0
// right : exists l0, sllseg(x, ?z, l0) at 1
// action : left_erase(0);
//          right_erase(1);
//          right_exist_add(l1);
//          right_add(sllseg(y, z, l1));
//          right_add(l0 == app(l, l1));

// id : 28
// priority : 4
// left : data_at(field_addr(?x, list, tail), ?y) at 0
// right : exists l, sllseg(x, ?z, l) at 1
// action : left_erase(0);
//          right_erase(1);
//          right_exist_add(l0);
//          right_exist_add(h);
//          right_add(data_at_head(x, h));
//          right_add(sllseg(y, z, l0));
//          instantiate(l -> cons(h, l0));

// id : 29
// priority : 3
// left : undef_data_at(?x) at 0
// right : data_at(x, ?y) at 1
// action : left_erase(0);
//          right_erase(1);

// id : 30
// priority : 3
// left : data_at(?x, ?y) at 0
// right : undef_data_at(x) at 1
// action : left_erase(0);
//          right_erase(1);
