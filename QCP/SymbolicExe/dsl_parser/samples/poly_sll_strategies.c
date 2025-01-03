//test curent rules
//max rule id:30

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
         left_add(data_at(field_addr(p, list, data), PTR(list), h));
         left_add(storeA(h, x));
         left_add(data_at(field_addr(p, list, next), PTR(list), y));
         left_add(sll{A}(storeA, y, l));
 
id : 11
priority : 3
right : sll{?A}(?storeA, p, cons{A}(x, l)) at 0
action : right_erase(0);
         right_exist_add(y);
         right_exist_add(h);
         right_add(data_at(field_addr(p, list, data), PTR(list), h));
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

