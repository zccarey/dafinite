// type client
// type server
datatype Server = Server(id:int, semaphore:bool)
datatype Client = Client(id:int, connServers:set<int>)
datatype DafnyState = DafnyState(clients:seq<Client>, servers:seq<Server>)

// relation link(X:client, Y:server)
// relation semaphore(X:server)
predicate RelationLink(m: DafnyState, c: Client, s: Server)
{
    && 0 <= s.id < |m.servers|
    && 0 <= c.id < |m.clients|
    && m.servers[s.id].id in m.clients[c.id].connServers
}

predicate RelationSemaphore(m: DafnyState, s: Server)
{
    && 0 <= s.id < |m.servers|
    && m.servers[s.id].semaphore
}

// after init {
//     semaphore(W) := true;
//     link(X,Y) := false
// }
predicate Init(m: DafnyState) {
    && forall s: Server :: s in m.servers ==> RelationSemaphore(m, s)
    && forall s: Server, c: Client :: s in m.servers && c in m.clients ==> !RelationLink(m, c, s)
}

// predicate ServerInit(s: Server, id: int) {
//     s.semaphore == true && s.id == id
// }

// predicate ClientInit(c: Client, id: int) {
//     |c.connServers| == 0  && c.id == id
// }

// predicate Connect(s: Server, s': Server, c: Client, c': Client) {
//     && s.id == s'.id
//     && c.id == c'.id
//     && s.semaphore == true
//     && s'.semaphore == false
//     && s.id in c'.connServers
// }

// action connect(x:client,y:server) = {
//   require semaphore(y);
//   link(x,y) := true;
//   semaphore(y) := false
// }
predicate ActionConnect(m: DafnyState, m': DafnyState) {
    exists c: Client, s: Server ::

        && RelationSemaphore(m, s) // in original state
        && RelationLink(m', c, s)
        && !RelationSemaphore(m', s)

        // TODO: might need to ensure client/server is in m.clients/m.servers on left side of implication
        && forall cf: Client, sf: Server :: (cf.id != c.id ==> RelationLink(m, cf, sf) == RelationLink(m', cf, sf))
        
        && forall sf: Server :: (sf.id != s.id ==> RelationSemaphore(m, sf) == RelationSemaphore(m', sf))


        /*
        && c in m.clients // client exists
        && s in m.servers // server exists
        && s.semaphore == true // server is unlocked to start
        && Client(c.id, c.connServers + {s.id}) in m'.clients // client ends up locked on this server
        && Server(s.id, false) in m'.servers // server ends up locked
        && (m.servers - {s}) == (m'.servers - {Server(s.id, false)}) // no other changes
        && (m.clients - {c}) == (m'.clients - {Client(c.id, c.connServers + {s.id})}) // no other changes
        */
}

// action disconnect(x:client,y:server) = {
//   require link(x,y);
//   link(x,y) := false;
//   semaphore(y) := true
// }
predicate ActionDisconnect(m: DafnyState, m': DafnyState) {
    exists c: Client, s: Server ::

        && !RelationSemaphore(m, s) // in original state
        && !RelationLink(m', c, s)
        && RelationSemaphore(m', s)

        && forall cf: Client, sf: Server :: (cf.id != c.id ==> RelationLink(m, cf, sf) == RelationLink(m', cf, sf))
        
        && forall sf: Server :: (sf.id != s.id ==> RelationSemaphore(m, sf) == RelationSemaphore(m', sf))

   /* && c in m.clients // client exists
    && s in m.servers // server exists
    && s.id in c.connServers // client held server lock
    && Client(c.id, c.connServers - {s.id}) in m'.clients // client ends up unlocked on this server
    && Server(s.id, true) in m'.servers // server ends up unlocked
    && (m.servers - {s}) == (m'.servers - {Server(s.id, true)}) // no other changes
    && (m.clients - {c}) == (m'.clients - {Client(c.id, c.connServers - {s.id})}) // no other changes*/
}

predicate Next(m:DafnyState, m':DafnyState) {
    //|| (exists c:Client, s:Server :: Connect(m, m', c, s))
    //|| (exists c:Client, s:Server :: Disconnect(m, m', c, s))
    || ActionConnect(m, m')
    || ActionDisconnect(m, m')
}

// export connect
// export disconnect

// invariant [1000000] link(C1, S) & link(C2, S) -> C1 = C2
lemma Invariant(m: DafnyState) 
    ensures forall c1: Client, c2:Client, s: Server :: 
    (c1 in m.clients && c2 in m.clients && s in m.servers) ==> (RelationLink(m, c1, s) && RelationLink(m, c2, s) ==> c1.id == c2.id)
{
    // somehow need to prove that safety property
}

