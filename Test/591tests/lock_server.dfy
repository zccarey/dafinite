datatype Server = Server(id:int, semaphore:bool)
datatype Client = Client(id:int, connServers:set<int>)
datatype DafnyState = DafnyState(clients:seq<Client>, servers:seq<Server>)

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

// c1 should be not changing if it is != c2
// predicate RelationLinkStable(m : DafnyState, m' : DafnyState, c1: Client, c2: Client, s: Server) {
//     c1.id != c2.id ==> RelationLink(m, c1, s) == RelationLink(m', c1, s)  link_c1_s_next
// }

predicate RelationDifferentClients(m: DafnyState, c1: Client, c2: Client){
    c1.id != c2.id
}

predicate RelationDifferentServers(m: DafnyState, s1: Server, s2: Server){
    s1.id != s2.id
}

predicate RelationServerExists(m: DafnyState, s: Server){
    s in m.servers
}

predicate RelationClientExists(m: DafnyState, c: Client){
    c in m.clients
}

predicate Init(m: DafnyState) {
    // && (forall s: Server :: s in m.servers ==> RelationSemaphore(m, s))
    && (forall s: Server :: RelationServerExists(m, s) ==> RelationSemaphore(m, s))
    // && (forall s: Server, c: Client :: s in m.servers && c in m.clients ==> !RelationLink(m, c, s))
    && (forall s: Server, c: Client :: ((RelationServerExists(m, s) && RelationClientExists(m, c)) ==> !RelationLink(m, c, s)))
}

predicate ActionConnect(m: DafnyState, m': DafnyState) {
    exists c: Client, s: Server ::

        && RelationSemaphore(m, s) // in original state
        && RelationLink(m', c, s)
        && !RelationSemaphore(m', s)

        // TODO: might need to ensure client/server is in m.clients/m.servers on left side of implication
        // && forall cf: Client, sf: Server :: (cf.id != c.id ==> RelationLink(m, cf, sf) == RelationLink(m', cf, sf))
        // && forall cf: Client, sf: Server :: RelationLinkStable(m, cf, c, sf)
        && forall cf: Client, sf: Server :: (RelationDifferentClients(m, cf, c) ==> RelationLink(m, cf, sf) == RelationLink(m', cf, sf))
        
        && forall sf: Server :: (RelationDifferentServers(m, sf, s) ==> RelationSemaphore(m, sf) == RelationSemaphore(m', sf))
}

predicate ActionDisconnect(m: DafnyState, m': DafnyState) {
    exists c: Client, s: Server ::

        && !RelationSemaphore(m, s) // in original state
        && !RelationLink(m', c, s)
        && RelationSemaphore(m', s)

        && forall cf: Client, sf: Server :: (RelationDifferentClients(m, cf, c) ==> RelationLink(m, cf, sf) == RelationLink(m', cf, sf))
        
        && forall sf: Server :: (RelationDifferentServers(m, sf, s) ==> RelationSemaphore(m, sf) == RelationSemaphore(m', sf))

}

predicate Next(m:DafnyState, m':DafnyState) {
    || ActionConnect(m, m')
    || ActionDisconnect(m, m')
}


lemma Invariant(m: DafnyState) 
    ensures forall c1: Client, c2:Client, s: Server :: 
    (RelationClientExists(m, c1) && RelationClientExists(m, c2) && RelationServerExists(m, s)) ==> (RelationLink(m, c1, s) && RelationLink(m, c2, s) ==> !RelationDifferentClients(m, c1, c2))
{
    // somehow need to prove that safety property
}


