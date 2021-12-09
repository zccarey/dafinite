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

predicate RelationServerExists(m: DafnyState, s: Server){
    s in m.servers
}

predicate RelationClientExists(m: DafnyState, c: Client){
    c in m.clients
}

predicate RelationClientEquals(m: DafnyState, c1: Client, c2: Client){
    && c1 in m.clients
    && c2 in m.clients
    && c1.id == c2.id
}

predicate RelationServerEquals(m: DafnyState, s1: Server, s2: Server){
    && s1 in m.servers
    && s2 in m.servers
    && s1.id == s2.id
}

predicate Init(m: DafnyState) {
    && (forall s: Server :: RelationServerExists(m, s) ==> RelationSemaphore(m, s))
    && (forall s: Server, c: Client :: ((RelationServerExists(m, s) && RelationClientExists(m, c)) ==> !RelationLink(m, c, s)))
}

predicate ActionConnect(m: DafnyState, m': DafnyState) {
	exists c: Client, s: Server ::
        && RelationSemaphore(m, s) // in original state
        && RelationLink(m', c, s)
        && !RelationSemaphore(m', s)

        // RelationLink does not change for all other client/server pairs
        && (forall cf: Client, sf: Server :: (!RelationClientEquals(m, cf, c) ==> (RelationLink(m, cf, sf) == RelationLink(m', cf, sf))))
        
        // RelationSemaphore does not change for all other servers
        && (forall sf: Server :: (!RelationServerEquals(m, sf, s) ==> (RelationSemaphore(m, sf) == RelationSemaphore(m', sf))))
}

predicate ActionDisconnect(m: DafnyState, m': DafnyState) {
    exists c: Client, s: Server ::
		&& RelationLink(m, c, s)
        && !RelationLink(m', c, s)
        && RelationSemaphore(m', s)

        // RelationLink does not change for all other client/server pairs
        && (forall cf: Client, sf: Server :: (!RelationClientEquals(m, cf, c) ==> (RelationLink(m, cf, sf) == RelationLink(m', cf, sf))))
        
        // RelationSemaphore does not change for all other servers
        && (forall sf: Server :: (!RelationServerEquals(m, sf, s) ==> (RelationSemaphore(m, sf) == RelationSemaphore(m', sf))))
}

predicate Next(m:DafnyState, m':DafnyState) {
    || ActionConnect(m, m')
    || ActionDisconnect(m, m')
}


predicate Safety(m: DafnyState)
{
    forall c1: Client, c2:Client, s: Server :: ((RelationClientExists(m, c1) && RelationClientExists(m, c2) && RelationServerExists(m, s)) ==> ((RelationLink(m, c1, s) && RelationLink(m, c2, s)) ==> RelationClientEquals(m, c1, c2)))
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
