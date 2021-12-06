//#instructor The switch is an example of a very simple state machine.
//#instructor All its steps are non-parameterized.
//#instructor This example is intended to show the basic of the boilerplate
//#instructor of a TLA+ state machine embedded in Dafny.

datatype SwitchState = On | Off

datatype DafnyState = Whatever(switch:SwitchState)

predicate RelationSwitchOn(v: DafnyState) {
    v.switch == On
}

predicate Init(v:DafnyState) {
    // v.switch == Off
    !RelationSwitchOn(v)
}

predicate ActionActivate(v:DafnyState, v':DafnyState) {
    // v'.switch == On
    RelationSwitchOn(v')
}

predicate ActionDeactivate(v:DafnyState, v':DafnyState) {
    // v'.switch == Off
    !RelationSwitchOn(v')
}

predicate ActionToggle(v:DafnyState, v':DafnyState) {
    // v'.switch == if v.switch.On? then Off else On
    RelationSwitchOn(v') != RelationSwitchOn(v)
}

predicate Next(v:DafnyState, v':DafnyState) {
    || ActionActivate(v, v')
    || ActionDeactivate(v, v')
    || ActionToggle(v, v')
}