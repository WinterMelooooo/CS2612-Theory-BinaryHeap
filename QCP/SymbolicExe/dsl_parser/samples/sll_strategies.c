//test curent rules
//max rule id:30

id : 4
priority : 0
left : sll(NULL, ?l) at 0
action : left_erase(0);
         left_add(l == nil{Z});
 
id : 5
priority : 0
right : sll(NULL, ?l) at 0
action : right_erase(0);
         right_add(l == nil{Z});

id : 7
priority : 2
left : sll(?p, ?l0) at 0
right : sll(p, ?l1) at 1
action : left_erase(0);
         right_erase(1);
         right_add(l0 == l1);

id : 8
priority : 4
left : sll(?p, ?l) at 0
       (p != NULL || NULL != p) at 1
action : left_erase(0);
         left_exist_add(x);
         left_exist_add(l0);
         left_add(sll(p, cons{Z}(x, l0)));
         left_add(l == cons{Z}(x, l0));
 
id : 9
priority : 4
left : (?p != NULL || NULL != ?p) at 0
right : sll(p, ?l) at 1
action : right_erase(1);
         right_exist_add(x);
         right_exist_add(l0);
         right_add(sll(p, cons{Z}(x, l0)));
         right_add(l == cons{Z}(x, l0));
 
 
id : 10
priority : 3
left : sll(p, cons{Z}(x, l)) at 0
action : left_erase(0);
         left_exist_add(y);
         left_exist_add(h);
         left_add(data_at(field_addr(p, list, data), I32, h));
         left_add(data_at(field_addr(p, list, next), PTR(list), y));
         left_add(sll(y, l));
 
id : 11
priority : 3
right : sll(p, cons{Z}(x, l)) at 0
action : right_erase(0);
         right_exist_add(y);
         right_exist_add(h);
         right_add(data_at(field_addr(p, list, data), I32, h));
         right_add(data_at(field_addr(p, list, next), PTR(list), y));
         right_add(sll(y, l));

id : 14
priority : 1
right : sllseg(?p, p, ?l) at 0
        sll(p, ?l0) at 1
action : right_erase(0);
         right_add(l == nil{Z});

id : 15
priority : 1
right : sllseg(?p, p, ?l) at 0
        data_at(field_addr(p, list, data), I32, ?h) at 1
action : right_erase(0);
         right_add(l == nil{Z});

id : 16
priority : 1
right : sllbseg(?p, p, ?l) at 0
        data_at(p, PTR(list), ?q) at 1
action : right_erase(0);
         right_add(l == nil{Z});

id : 17
priority : 1
left : sllbseg(?p, ?q, ?l1) at 0
       data_at(q, PTR(list), ?v1) at 1
right : sllbseg(p, q, ?l2) at 2
        data_at(q, PTR(list), ?v2) at 3
action : left_erase(0);
         right_erase(2);
         right_add(l1 == l2);
         
id : 18
priority : 1
left : sllbseg(?p, ?q, ?l1) at 0
       data_at(q, PTR(list), ?v1) at 1
right : sllbseg(p, q, ?l2) at 2
        data_at(q, PTR(list), ?v2) at 3
action : left_erase(0);
         right_erase(2);
         right_add(l1 == l2);

