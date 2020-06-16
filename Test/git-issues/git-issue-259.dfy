

module {:extern "M"} M {
    datatype M = M(x : nat)
}

method Main() {
    var M := M.M(3);
}
