#lang forge/temporal
option max_tracelength 10

abstract sig CustomerStatus {}
one sig Waiting, Seated, Ordered, Ready4Check extends CustomerStatus {} //state changes

abstract sig Person {}
sig Customer extends Person {
  // can either be empty or contain exactly one
  // myTableNumber: lone Table, 
  var status: one CustomerStatus
  //should each customer have an order?? instead of having orders in the Table sig
}

pred customer_init {
  all c: Customer | c.status = Waiting
}

pred customerTransistion {
  some c: Customer | {
    // some changed: CustomerStatus | {
      c.status = Waiting => c.status' = Seated
      c.status = Seated => c.status' = Ordered
      c.status = Ordered => c.status' = Ready4Check
      c.status = Ready4Check => c.status' = Waiting
      all other: Customer-c | other.status = other.status' }
}

run{customer_init and always customerTransistion}