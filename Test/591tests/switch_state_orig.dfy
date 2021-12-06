//#instructor The switch is an example of a very simple state machine.
//#instructor All its steps are non-parameterized.
//#instructor This example is intended to show the basic of the boilerplate
//#instructor of a TLA+ state machine embedded in Dafny.

datatype SwitchState = On | Off

datatype Variables = Variables(switch:SwitchState)

predicate Init(v:Variables) {
    v.switch == Off
}

predicate Activate(v:Variables, v':Variables) {
    v'.switch == On
}

predicate Deactivate(v:Variables, v':Variables) {
    v'.switch == Off
}

predicate Toggle(v:Variables, v':Variables) {
    v'.switch == if v.switch.On? then Off else On
}

predicate Next(v:Variables, v':Variables) {
    || Activate(v, v')
    || Deactivate(v, v')
    || Toggle(v, v')
}