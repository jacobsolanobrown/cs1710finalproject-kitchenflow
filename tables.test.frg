#lang forge

open "tables.frg"

test suite for valid_state {
    assert wrapperInvalid is necessary for valid_state
}

pred invalidState { some t: Table | {
    t in Available.tables and t in Full.tables }
}
pred wrapperInvalid {not invalidState}
test suite for server_init {}

test suite for table_init {}


