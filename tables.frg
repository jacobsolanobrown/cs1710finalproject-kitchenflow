#lang forge
option problem_type temporal 

abstract sig Person {}

sig Customer extends Person {
  tn: lone Table
}
sig Server extends Person {
  // tables: set Table
  //not sure if we need this
  // activeOrders: set Dish
}

sig Table {
  tableNumber: one Int,
  seatNum: one Int,
  customers: set Customer, 
  // server: one Server,
  // orders: set Dish,
  status: one TableStatus
  // price: lone Int
}

abstract sig TableStatus {}
one sig Available, Full extends TableStatus {}

/*
Initializes tables at the beginning of the day --> they are all available with no one at them!  
*/
pred valid_table_init {
  // 1 tables rn 
  // ?? enforce unique table numbers  
  //assigns table numbers, marks table available & w/no origional customers 
  all t: Table | {
    //assign unique table number 
    
    //assign seats available 
    t1.tableNumber > 0 and t1.tableNumber < 6
    t1.tableNumber != t2.tableNumber 
  }

  // t.tableNumber > 0 and t.tableNumber < 4 and t.status = Available and no customers and t.seatNum > 0 and t.seatNum <= 4
  all c: Customer | no c.tn  
}

// pred ValidTone {
//     all n: Note | n.tone >= 0 and n.tone < 12 and n.next != n
//     // all n: Note | n.next != n.prev
// }
pred table_setup {
  valid_table_init
}

run {table_setup} for 5 Int, exactly 4 Table
