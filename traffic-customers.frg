#lang forge/temporal
option max_tracelength 10

abstract sig CustomerStatus {} // color
one sig Waiting, Seated, Ordered, Ready4Check extends CustomerStatus {}
abstract sig Person { // light
    var status: one CustomerStatus
}
one sig customer extends Person {}

pred init { all l: Person | l.status = Waiting }
pred delta {
    some changed: Person | {
        changed.status = Waiting => changed.status' = Seated
        changed.status = Seated => changed.status' = Ordered 
        changed.status = Ordered => changed.status' = Ready4Check 
        changed.status = Ready4Check => changed.status' = Waiting
        //changed.status = Green => changed.status' = Yellow 
        all other: Person-changed | other.status = other.status' } }
run { init and always delta }

/* Some formulas we tried include:
  - eventually always {EW.color = Green}
  - EW.color'''' = NS.color'
  - next_state EW.color = NS.color

  - prev_state next_state EW.color = NS.color 
  - next_state EW.color = NS.color prev_state 
    ^ Note these last two did _not_ produce the same result! 

  - until (see notes)
*/