datatype Server = Server(id:int, semaphore:bool)
datatype Client = Client(id:int, connServers:set<Server>)
datatype DafnyState = DafnyState(clients:set<Client>, servers:set<Server>)

predicate NoOtherLinkChange(m: DafnyState, m': DafnyState, c: Client, s: Server){
    // c and s are 2 objects being modified, make sure no others change
    (forall c_: Client, c_': Client, s_: Server, s_': Server :: 
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
}

predicate NoOtherSemaphoreChange(m: DafnyState, m': DafnyState, s: Server){
    (forall s_: Server, s_': Server ::
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

predicate Init(m: DafnyState) {
    // Don't need to check IDs.
    // Holding semaphore / connServers constant means existence of multiple items in set implies they have different IDs
    // (because there are no duplicates)
    && (forall s: Server :: s in m.servers ==> s.semaphore)
    && (forall c: Client, s: Server :: (c in m.clients && s in m.servers) ==> (s !in c.connServers))
}

predicate ActionConnect(m: DafnyState, m': DafnyState) {
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

        && NoOtherLinkChange(m, m', c, s)
        
        && NoOtherSemaphoreChange(m, m', s)
}

predicate ActionDisconnect(m: DafnyState, m': DafnyState) {
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
		&& s' !in c'.connServers // the client and server are not linked
		&& s'.semaphore            // the server's semaphore is true

		// requirements on the rest of the state not changing

		&& NoOtherLinkChange(m, m', c, s)
		
		&& NoOtherSemaphoreChange(m, m', s)
}

predicate Next(m:DafnyState, m':DafnyState) {
    || ActionConnect(m, m')
    || ActionDisconnect(m, m')
}


predicate Safety(m: DafnyState)
{
    forall c1: Client, c2: Client, s: Server :: (
        (c1 in m.clients && c2 in m.clients && s in m.servers) ==>
        ((s in c1.connServers && s in c2.connServers) ==> c1.id == c2.id)
    )
}