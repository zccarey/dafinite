datatype Node = Node(id: int, vote_y: bool, vote_n: bool, alive: bool, rcvd_commit: bool, rcvd_abort: bool, commit:bool, abort:bool)
datatype DafnyState = DafnyState(nodes: set<Node>)

predicate NodesExistAndAreSame(m: DafnyState, m': DafnyState, n: Node, n': Node){
    && n in m.nodes
    && n' in m'.nodes
    && n.id == n'.id
}

predicate NoOtherNodeChanges(m: DafnyState, m': DafnyState, n: Node){
    forall n_ : Node, n_' : Node ::
    (
        (
            && NodesExistAndAreSame(m, m', n_, n_')
            && n.id != n_.id
        )
        ==>
        (
            && n_.vote_y == n_'.vote_y
            && n_.vote_n == n_'.vote_n
            && n_.alive == n_'.alive
            && n_.rcvd_commit == n_'.rcvd_commit
            && n_.rcvd_abort == n_'.rcvd_abort
            && n_.commit == n_'.commit
            && n_.abort == n_'.abort
        )
        
    )

}

predicate Init(m: DafnyState){
    forall n: Node ::
    (
        && n.vote_y == false
        && n.vote_n == false
        && n.commit == false
        && n.abort == false
        && n.rcvd_abort == false
        && n.rcvd_commit == false
        && n.alive == true
    )
}

predicate ActionVoteYes(m: DafnyState, m': DafnyState){
    exists n: Node, n': Node ::
    (
        && NodesExistAndAreSame(m, m', n, n')
        
        // reqs on prev state
        && n.alive
        && !n.vote_n
        && !n.commit
        && !n.abort
        // TODO TODO TODO do we care if they have rcvd anything?

        // reqs on next state
        && n'.vote_y

        // nothing else changed
        && n.alive == n'.alive
        && n.vote_n == n'.vote_n
        && n.commit == n'.commit
        && n.abort == n'.abort
        && n.rcvd_commit == n'.rcvd_commit
        && n.rcvd_abort == n'.rcvd_abort

        && NoOtherNodeChanges(m, m', n)
    )
}

predicate ActionVoteNo(m: DafnyState, m': DafnyState){
    exists n: Node, n': Node ::
    (
        && NodesExistAndAreSame(m, m', n, n')
        
        // reqs on prev state
        && n.alive
        && !n.vote_y
        && !n.commit
        && !n.abort
        // TODO TODO TODO do we care if they have rcvd anything?

        // reqs on next state
        && n'.vote_n

        // nothing else changed
        && n.alive == n'.alive
        && n.vote_y == n'.vote_y
        && n.commit == n'.commit
        && n.abort == n'.abort
        && n.rcvd_commit == n'.rcvd_commit
        && n.rcvd_abort == n'.rcvd_abort

        && NoOtherNodeChanges(m, m', n)
    )
}

predicate ActionCoordinatorSendCommit(m: DafnyState, m': DafnyState){
    forall n: Node, n': Node ::
    (
        (
            NodesExistAndAreSame(m, m', n, n')
        )
        ==>
        (
            // reqs on prev state
            && !n.rcvd_commit
            && !n.rcvd_abort
            && n.vote_y

            // reqs on next state
            && n'.rcvd_commit
            
            // nothing else changed
            && n.alive == n'.alive
            && n.rcvd_abort == n'.rcvd_abort
            && n.vote_n == n'.vote_n
            && n.vote_y == n'.vote_y
            && n.commit == n'.commit
            && n.abort == n'.abort
        )
    )
}

predicate ActionCoordinatorSendAbort(m: DafnyState, m': DafnyState){
    && forall n: Node, n': Node ::
    (
        (
            NodesExistAndAreSame(m, m', n, n')
        )
        ==>
        (
            // reqs on prev state
            && !n.rcvd_commit
            && !n.rcvd_abort

            // reqs on next state
            && n'.rcvd_abort
            
            // nothing else changed
            && n.alive == n'.alive
            && n.rcvd_commit == n'.rcvd_commit
            && n.vote_n == n'.vote_n
            && n.vote_y == n'.vote_y
            && n.commit == n'.commit
            && n.abort == n'.abort
        )
    )

    // can't trivially abort
    && exists n_ : Node ::
    (
        && n_ in m.nodes
        && (!n_.alive || n_.vote_n)
    )
}

predicate ActionCommit(m: DafnyState, m': DafnyState){
    exists n: Node, n': Node ::
    (
        && NodesExistAndAreSame(m, m', n, n')
        
        // reqs on prev state
        && n.alive
        && n.rcvd_commit

        // reqs on next state
        && n'.commit

        // nothing else changed
        && n.alive == n'.alive
        && n.vote_y == n'.vote_y
        && n.vote_n == n'.vote_n
        && n.abort == n'.abort
        && n.rcvd_commit == n'.rcvd_commit
        && n.rcvd_abort == n'.rcvd_abort

        && NoOtherNodeChanges(m, m', n)
    )


}

predicate ActionAbort(m: DafnyState, m': DafnyState){
    exists n: Node, n': Node ::
    (
        && NodesExistAndAreSame(m, m', n, n')
        
        // reqs on prev state
        && n.alive
        && n.rcvd_abort

        // reqs on next state
        && n'.abort

        // nothing else changed
        && n.alive == n'.alive
        && n.vote_y == n'.vote_y
        && n.vote_n == n.vote_n
        && n.commit == n'.commit
        && n.rcvd_commit == n'.rcvd_commit
        && n.rcvd_abort == n'.rcvd_abort

        && NoOtherNodeChanges(m, m', n)
    )
    
}

predicate ActionNodeFail(m: DafnyState, m': DafnyState){
    exists n: Node, n': Node ::
    (
        && NodesExistAndAreSame(m, m', n, n')

        && n.alive
        && !n'.alive

        // nothing else changed
        && n.vote_n == n'.vote_n
        && n.vote_y == n'.vote_y
        && n.commit == n'.commit
        && n.abort == n'.abort
        && n.rcvd_abort == n'.rcvd_abort
        && n.rcvd_commit == n'.rcvd_commit

        && NoOtherNodeChanges(m, m', n)
    )
}

predicate Next(m: DafnyState, m': DafnyState){
    || ActionAbort(m, m')
    || ActionNodeFail(m, m')
    || ActionCommit(m, m')
    || ActionVoteNo(m, m')
    || ActionVoteYes(m, m')
    || ActionCoordinatorSendAbort(m, m')
    || ActionCoordinatorSendCommit(m, m')
}

predicate Safety(m: DafnyState){
    forall n1: Node, n2: Node ::
    (
        (
            && n1 in m.nodes
            && n2 in m.nodes
            && n1.id != n2.id
        )
        ==>
        (
            && (n1.commit ==> !n2.abort)
            && (n1.commit ==> n2.vote_y)
        )
    )
}

