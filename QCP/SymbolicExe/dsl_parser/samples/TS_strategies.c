id : 1
priority : normal(0)
left : data_at(field_addr(field_addr(?u, TU, U1), TS, S1), I32, ?x) at 0
       data_at(field_addr(field_addr(u, TU, U1), TS, S2), I32, ?y) at 1
right : data_at(field_addr(field_addr(u, TU, U2), TS, S1), I32, ?z) at 2
action : left_erase(0);
         left_erase(1);
         left_exist_add(a);
         left_exist_add(b);
         left_add(data_at(field_addr(field_addr(u, TU, U2), TS, S1), I32, a));
         left_add(data_at(field_addr(field_addr(u, TU, U2), TS, S2), I32, b));

id : 2
priority : normal(0)
left : data_at(field_addr(field_addr(?u, TU, U1), TS, S1), I32, ?x) at 0
       data_at(field_addr(field_addr(u, TU, U1), TS, S2), I32, ?y) at 1
right : data_at(field_addr(field_addr(u, TU, U2), TS, S2), I32, ?z) at 2
action : left_erase(0);
         left_erase(1);
         left_exist_add(a);
         left_exist_add(b);
         left_add(data_at(field_addr(field_addr(u, TU, U2), TS, S1), I32, a));
         left_add(data_at(field_addr(field_addr(u, TU, U2), TS, S2), I32, b));

id : 3
priority : normal(0)
left : data_at(field_addr(field_addr(?u, TU, U2), TS, S1), I32, ?x) at 0
       data_at(field_addr(field_addr(u, TU, U2), TS, S2), I32, ?y) at 1
right : data_at(field_addr(field_addr(u, TU, U1), TS, S1), I32, ?z) at 2
action : left_erase(0);
         left_erase(1);
         left_exist_add(a);
         left_exist_add(b);
         left_add(data_at(field_addr(field_addr(u, TU, U1), TS, S1), I32, a));
         left_add(data_at(field_addr(field_addr(u, TU, U1), TS, S2), I32, b));

id : 4
priority : normal(0)
left : data_at(field_addr(field_addr(?u, TU, U2), TS, S1), I32, ?x) at 0
       data_at(field_addr(field_addr(u, TU, U2), TS, S2), I32, ?y) at 1
right : data_at(field_addr(field_addr(u, TU, U1), TS, S2), I32, ?z) at 2
action : left_erase(0);
         left_erase(1);
         left_exist_add(a);
         left_exist_add(b);
         left_add(data_at(field_addr(field_addr(u, TU, U1), TS, S1), I32, a));
         left_add(data_at(field_addr(field_addr(u, TU, U1), TS, S2), I32, b));

id : 5
priority : normal(0)
left : StoreTS(field_addr(?u, TU, U1), ?x, ?y) at 0
right : data_at(field_addr(field_addr(u, TU, U1), TS, S1), ?z) at 1
action : left_erase(0);
         left_add(data_at(field_addr(field_addr(u, TU, U1), TS, S1), I32, x));
         left_add(partial_store_TS_missing1(field_addr(u, TU, U1), y));

id : 6
priority : normal(0)
left : StoreTS(field_addr(?u, TU, U1), ?x, ?y) at 0
right : data_at(field_addr(field_addr(u, TU, U1), TS, S2), ?z) at 1
action : left_erase(0);
         left_add(data_at(field_addr(field_addr(u, TU, U1), TS, S2), I32, y));
         left_add(partial_store_TS_missing2(field_addr(u, TU, U1), x));

id : 7 
priority : normal(0)
left : StoreTS(field_addr(?u, TU, U1), ?x, ?y) at 0
right : data_at(field_addr(field_addr(u, TU, U2), TS, S1), ?z) at 1
action : left_erase(0);
         left_exist_add(a);
         left_exist_add(b);
         left_add(data_at(field_addr(field_addr(u, TU, U2), TS, S1), I32, a));
         left_add(partial_store_TS_missing1(field_addr(u, TU, U2), b));

id : 8
priority : normal(0)
left : StoreTS(field_addr(?u, TU, U1), ?x, ?y) at 0
right : data_at(field_addr(field_addr(u, TU, U2), TS, S2), ?z) at 1
action : left_erase(0);
         left_exist_add(a);
         left_exist_add(b);
         left_add(data_at(field_addr(field_addr(u, TU, U2), TS, S2), I32, b));
         left_add(partial_store_TS_missing2(field_addr(u, TU, U2), a));

id : 9
priority : normal(0)
left : StoreTS(field_addr(?u, TU, U2), ?x, ?y) at 0
right : data_at(field_addr(field_addr(u, TU, U2), TS, S1), ?z) at 1
action : left_erase(0);
         left_add(data_at(field_addr(field_addr(u, TU, U2), TS, S1), I32, x));
         left_add(partial_store_TS_missing1(field_addr(u, TU, U2), y));

id : 10
priority : normal(0)
left : StoreTS(field_addr(?u, TU, U2), ?x, ?y) at 0
right : data_at(field_addr(field_addr(u, TU, U2), TS, S2), ?z) at 1
action : left_erase(0);
         left_add(data_at(field_addr(field_addr(u, TU, U2), TS, S2), I32, y));
         left_add(partial_store_TS_missing2(field_addr(u, TU, U2), x));

id : 11
priority : normal(0)
left : StoreTS(field_addr(?u, TU, U2), ?x, ?y) at 0
right : data_at(field_addr(field_addr(u, TU, U1), TS, S1), ?z) at 1
action : left_erase(0);
         left_exist_add(a);
         left_exist_add(b);
         left_add(data_at(field_addr(field_addr(u, TU, U1), TS, S1), I32, a));
         left_add(partial_store_TS_missing1(field_addr(u, TU, U1), b));

id : 12
priority : normal(0)
left : StoreTS(field_addr(?u, TU, U2), ?x, ?y) at 0
right : data_at(field_addr(field_addr(u, TU, U1), TS, S2), ?z) at 1
action : left_erase(0);
         left_exist_add(a);
         left_exist_add(b);
         left_add(data_at(field_addr(field_addr(u, TU, U1), TS, S2), I32, b));
         left_add(partial_store_TS_missing2(field_addr(u, TU, U1), a));

id : 13
priority : post(1)
left : data_at(field_addr(field_addr(u, TU, U1), TS, S1), ?x) at 0
       partial_store_TS_missing1(field_addr(u, TU, U1), ?y) at 1
action : left_erase(0);
         left_erase(1);
         left_add(StoreTS(field_addr(u, TU, U1), x, y));

id : 14
priority : post(1)
left : data_at(field_addr(field_addr(u, TU, U1), TS, S2), ?y) at 0
       partial_store_TS_missing2(field_addr(u, TU, U1), ?x) at 1
action : left_erase(0);
         left_erase(1);
         left_add(StoreTS(field_addr(u, TU, U1), x, y));

id : 15
priority : post(1)
left : data_at(field_addr(field_addr(u, TU, U2), TS, S1), ?x) at 0
       partial_store_TS_missing1(field_addr(u, TU, U2), ?y) at 1
action : left_erase(0);
         left_erase(1);
         left_add(StoreTS(field_addr(u, TU, U2), x, y));

id : 16
priority : post(1)
left : data_at(field_addr(field_addr(u, TU, U2), TS, S2), ?y) at 0
       partial_store_TS_missing2(field_addr(u, TU, U2), ?x) at 1
action : left_erase(0);
         left_erase(1);
         left_add(StoreTS(field_addr(u, TU, U2), x, y));