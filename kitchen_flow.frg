#lang forge/temporal

option verbose 5

------------- DEFINITIONS -------------
-------- Employees & Customers --------

abstract sig Person {
  // name one: String 
  // phoneNumber: lone String
}
sig Chef extends Person {
  // canCook: set Dish
  // numOfDishes/experianceLevel
}
sig Customer extends Person {
  tn: lone Table
  // order: set Dish
}
sig Server extends Person {
  tables: set Table
  //not sure if we need this
  // activeOrders: set Dish
}

------------ Dishes / Menu ------------

// abstract sig Dish {
//    price: one Int
// }
// sig Burger extends Dish {}
// sig Salad extends Dish {}
// sig ChickTenders extends Dish {}

---------------- Table ----------------

// sig DiningRoom {
//   tables: set Table
// }

sig Table {
  tableNumber: one Int,
  customers: set Customer, 
  server: one Server,
  // orders: set Dish,
  status: one TableStatus
  // price: lone Int
}

abstract sig TableStatus {}
one sig Available, Full extends TableStatus {}

---------------- Kitchen ----------------

sig Kitchen {
  var chefs: set Chef, 
  //first in first out 
  var orders: one Queue,
  //queue based on something else! 
  var tables: one Queue, 
  var TicketTime: one Int 
}

-----------------------------------------
-------------- INIT STATE ---------------

//all tables get assigned a number and are open 
pred init_tables {
   all t: Table | { 
    all tn: tableNumber | {
      (tn < 1 or tn > 6) => {
        no t.tableNumber
    } 
  }
  }
}

----------- TABLE MANAGEMENT ------------

/*
Finds available tables with the required number of seats.
*/
// pred find_available_tables[num_seats: Int] {

// }

/*
Marks a table as occupied.
*/
// pred occupy_table[table_num: Int] {

// }

/*
Marks a table as empty once customers leave.
*/
// pred vacate_table[table_num: Int] {

// }

pred GWtraces { 
    init_tables
}

run {
  GWtraces
} for 5 Table, 4 Person

