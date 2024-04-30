#lang forge/temporal

------------- DEFINITIONS -------------
-------- Employees & Customers --------

abstract sig Person {}
sig Chef extends Person {}
sig Customer extends Person {}
sig Server extends Person {}

------------ Dishes / Menu ------------

abstract sig Dish {}
sig Burger extends Dish {}
sig Salad extends Dish {}
sig ChickTenders extends Dish {}

---------------- Table ----------------

sig Table {
  var customers: set Customer, 
  var server: one Server,
  var orders: set Dish,
  var status: one TableStatus 
}

abstract sig TableStatus {}
one sig Available extends TableStatus {}
one sig Full extends TableStatus {}

---------------- Kitchen ----------------

sig Kitchen {
  var chefs: set Chef, 
  //first in first out 
  // var orders: one Queue,
  //queue based on something else! 
  // var tables: one Queue, 
  var TicketTime: one Int 
}

-----------------------------------------


