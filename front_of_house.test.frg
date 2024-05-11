#lang forge
//assert and is sat/unsat/ is theorem

open "front_of_house.frg"

pred invalidState { some t: Table | {
    t in Available.tables and t in Full.tables }
}
pred wrapperInvalid {not invalidState}
test suite for valid_state {
  // test expect { possibleToMove: {
  //   valid_state
  //   #{Table} = add(#{vailable.tables}, #{Full.tables}) 
  // } is theorem }  
  assert wrapperInvalid is necessary for valid_state
}

test suite for server_init {

}

test suite for table_init {}

// test suite for  








