type Id = int

datatype Server = Server(id:Id, semaphore:bool)
datatype Client = Client(id:Id, connServers:set<Server>)
datatype DafnyState = DafnyState(clients:set<Client>, servers:set<Server>)

// predicate RelationLink(m: DafnyState, c: Client, s: Server)
// {
//     && 0 <= s.id < |m.servers|
//     && 0 <= c.id < |m.clients|
//     && m.servers[s.id].id in m.clients[c.id].connServers

//     // forall c_: Client, s_: Server :: (c_ in m.clients && c.id == c_.id) ==> ((s_ in m.servers && s.id == s_.id) ==> s_ in c_.connServers))
// }

// predicate RelationSemaphore(m: DafnyState, s: Server)
// {
//     && 0 <= s.id < |m.servers|
//     && m.servers[s.id].semaphore
// }

// predicate RelationServerExists(m: DafnyState, s: Server){
//     s in m.servers
// }

// predicate RelationClientExists(m: DafnyState, c: Client){
//     c in m.clients
// }

// predicate RelationClientEquals(m: DafnyState, c1: Client, c2: Client){
//     && c1 in m.clients
//     && c2 in m.clients
//     && c1.id == c2.id
// }

// predicate RelationServerEquals(m: DafnyState, s1: Server, s2: Server){
//     && s1 in m.servers
//     && s2 in m.servers
//     && s1.id == s2.id
// }

predicate Init(m: DafnyState) {
    //&& (forall s: Server :: RelationServerExists(m, s) ==> RelationSemaphore(m, s))
    //&& (forall s: Server, c: Client :: ((RelationServerExists(m, s) && RelationClientExists(m, c)) ==> !RelationLink(m, c, s)))

    // Don't need to check IDs.
    // Holding semaphore / connServers constant means existence of multiple items in set implies they have different IDs
    // (because there are no duplicates)
    && (forall s: Server :: s in m.servers ==> s.semaphore)
    && (forall c: Client, s: Server :: (c in m.clients && s in m.servers) ==> !(s in c.connServers))
}

predicate ActionConnect(m: DafnyState, m': DafnyState) {
    /*
	exists c: Client, s: Server ::
        && RelationSemaphore(m, s) // in original state
        && RelationLink(m', c, s)
        && !RelationSemaphore(m', s)

        // RelationLink does not change for all other client/server pairs
        && (forall cf: Client, sf: Server :: (!RelationClientEquals(m, cf, c) ==> (RelationLink(m, cf, sf) == RelationLink(m', cf, sf))))
        
        // RelationSemaphore does not change for all other servers
        && (forall sf: Server :: (!RelationServerEquals(m, sf, s) ==> (RelationSemaphore(m, sf) == RelationSemaphore(m', sf))))
    */

    exists c: Client, c': Client, s: Server, s': Server::

        && c.id == c'.id    // c and c' refer to same client
        && s.id == s'.id    // s and s' refer to same server
        && c in m.clients   // c is a client in the previous state
        && c' in m'.clients // c' is a client in the next state
        && s in m.servers   // s is a server in the previous state
        && s' in m.servers  // s' is a server in the next state

        // requirements on previous state
        && s.semaphore // the server's semaphore is true

        // requirements on next state
        && s' in c'.connServers // the client and server are linked
        && !s'.semaphore        // the server's semaphore is false

        // requirements on the rest of the state not changing

        && (forall c_: Client, c_': Client, s_: Server, s_': Server :: 
            (
                // c_ and s_ refer to another client server pair in the system
                (
                && c_ in m.clients
                && c_' in m'.clients
                && s_ in m.servers
                && s_' in m'.servers
                && c_.id == c_'.id
                && s_.id == s_'.id
                && (c_.id != c.id || s_.id != s.id)
                )
                ==>
                // link between client and server doesn't change
                ((s_ in c_.connServers) == (s_' in c_'.connServers))
            )
        )
        
        && (forall s_: Server, s_': Server ::
            (
                // s_ refers to another server in the system
                (
                && s_ in m.servers
                && s_' in m'.servers
                && s_.id == s_'.id
                && s_.id != s.id
                )
                ==>
                // server's semaphore doesn't change
                (s_.semaphore == s_'.semaphore)
            )
        )
}

predicate ActionDisconnect(m: DafnyState, m': DafnyState) {
    /*exists c: Client, s: Server ::
		&& RelationLink(m, c, s)
        && !RelationLink(m', c, s)
        && RelationSemaphore(m', s)

        // RelationLink does not change for all other client/server pairs
        && (forall cf: Client, sf: Server :: (!RelationClientEquals(m, cf, c) ==> (RelationLink(m, cf, sf) == RelationLink(m', cf, sf))))
        
        // RelationSemaphore does not change for all other servers
        && (forall sf: Server :: (!RelationServerEquals(m, sf, s) ==> (RelationSemaphore(m, sf) == RelationSemaphore(m', sf))))
    */
        exists c: Client, c': Client, s: Server, s': Server::

            && c.id == c'.id    // c and c' refer to same client
            && s.id == s'.id    // s and s' refer to same server
            && c in m.clients   // c is a client in the previous state
            && c' in m'.clients // c' is a client in the next state
            && s in m.servers   // s is a server in the previous state
            && s' in m.servers  // s' is a server in the next state

            // requirements on previous state
            && s in c.connServers // the client and server are linked

            // requirements on next state
            && !(s' in c'.connServers) // the client and server are not linked
            && s'.semaphore            // the server's semaphore is true

            // requirements on the rest of the state not changing

            && (forall c_: Client, c_': Client, s_: Server, s_': Server :: 
                (
                    // c_ and s_ refer to another client server pair in the system
                    (
                    && c_ in m.clients
                    && c_' in m'.clients
                    && s_ in m.servers
                    && s_' in m'.servers
                    && c_.id == c_'.id
                    && s_.id == s_'.id
                    && (c_.id != c.id || s_.id != s.id)
                    )
                    ==>
                    // link between client and server doesn't change
                    ((s_ in c_.connServers) == (s_' in c_'.connServers))
                )
            )
            
            && (forall s_: Server, s_': Server ::
                (
                    // s_ refers to another server in the system
                    (
                    && s_ in m.servers
                    && s_' in m'.servers
                    && s_.id == s_'.id
                    && s_.id != s.id
                    )
                    ==>
                    // server's semaphore doesn't change
                    (s_.semaphore == s_'.semaphore)
                )
            )
        
}

predicate Next(m:DafnyState, m':DafnyState) {
    || ActionConnect(m, m')
    || ActionDisconnect(m, m')
}


predicate Safety(m: DafnyState)
{
    // forall c1: Client, c2:Client, s: Server :: ((RelationClientExists(m, c1) && RelationClientExists(m, c2) && RelationServerExists(m, s)) ==> ((RelationLink(m, c1, s) && RelationLink(m, c2, s)) ==> RelationClientEquals(m, c1, c2)))
    forall c1: Client, c2: Client, s: Server :: (
        (c1 in m.clients && c2 in m.clients && s in m.servers) ==>
        ((s in c1.connServers && s in c2.connServers) ==> c1.id == c2.id)
    )
}

/*

// Notes from Manos re: proving protocols correct in Dafny, safety property vs.
// inductive invariants.

lemma InitImpliesInv(m: DafnyState)
    requires Init(m)
    ensures Inv(m)
{

}

lemma NextPreservesInv(m: DafnyState, m': DafnyState)
    requires Next(m, m')
    requires Inv(m)
    ensures Inv(m')
{

}

lemma InvImpliesSafety(m: DafnyState)
    requires Inv(m)
    ensures Safety(m)
{
}
*/
