
id : 15
priority : 0
left : data_at_head(?p, ?x) at 0
right : data_at(field_addr(p, list, head), x) at 1
action : left_erase(0);
         right_erase(1);

id : 16
priority : 0
left : data_at(field_addr(?p, list, head), ?x) at 0
right : data_at_head(p, x) at 1
action : left_erase(0);
         right_erase(1);

id : 17
priority : 0
left : data_at_tail(?p, ?x) at 0
right : data_at(field_addr(p, list, tail), x) at 1
action : left_erase(0);
         right_erase(1);

id : 18
priority : 0
left : data_at_(field_addr(?p, list, tail), ?x) at 0
right : data_at_tail(p, x) at 1
action : left_erase(0);
         right_erase(1);


//risk strategy: 19, 20
id : 19
priority : 3
left : lseg(?x, x, ?l) at 0
check : absense(x != NULL);
        absense(NULL != x);
action : left_erase(0);
         right_add(l == nil);

id : 20
priority : 3
right : lseg(?x, x, ?l) at 0
check : absense(x != NULL);
        absense(NULL != x);
action : right_erase(0);
         right_add(l == nil);

id : 21
priority : 1
right : exists l, lseg(?x, x, l) at 0
check : absense(x != NULL);
        absense(NULL != x);
action : right_erase(0);
         instantiate(l -> nil);

id : 22
priority : 3
left : lseg(?x, ?y, ?l) at 0
right : lseg(x, ?z, ?l0) at 1
action : left_erase(0);
         right_erase(1);
         right_exist_add(l1);
         right_add(lseg(y, z, l1));
         right_add(l0 == app(l, l1));