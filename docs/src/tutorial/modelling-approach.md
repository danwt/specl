# How to Think About Modelling

A spec defines a state machine: an initial state, a set of actions (transitions), and invariants (safety properties). The model checker exhaustively explores every reachable state via BFS. If an invariant is violated, it produces the shortest trace leading to the violation.

## The modelling process

### 1. Identify the state

What variables fully describe the system? For N processes, use `Dict[Int, ...]` keyed by process ID.

```specl
var role: Dict[Int, Int]         // per-process role (e.g., 0=follower, 1=candidate, 2=leader)
var log: Dict[Int, Seq[Int]]     // per-process log
var msgs: Set[Seq[Int]]          // message set (global)
```

### 2. Identify the actions

What can happen? Each action is a possible state transition. Use parameters to model nondeterminism — which process acts, which message is received, what value is chosen.

```specl
action Timeout(i: 0..N) { ... }           // any process can time out
action SendVote(src: 0..N, dst: 0..N) { ... }  // any pair can communicate
action ChooseValue(v: 0..MAX) { ... }      // nondeterministic choice
```

### 3. Write guards

`require` restricts when actions can fire. This is where you encode protocol preconditions.

```specl
action BecomeLeader(i: 0..N) {
    require role[i] == 1                                          // must be candidate
    require len({k in 0..N if votesGranted[i][k]}) * 2 > N + 1   // must have quorum
    role = role | {i: 2}
}
```

### 4. Write invariants

What must always hold? Safety properties go here.

```specl
invariant ElectionSafety {
    all i in 0..N: all j in 0..N:
        (role[i] == 2 and role[j] == 2 and currentTerm[i] == currentTerm[j])
            implies i == j
}
```

### 5. Start small

State spaces grow exponentially. Always start with `N=2` and small bounds, verify correctness, then scale up for higher confidence.

```bash
specl check spec.specl -c N=2 -c MaxTerm=1    # start here
specl check spec.specl -c N=2 -c MaxTerm=2    # scale up
specl check spec.specl -c N=3 -c MaxTerm=2 --por --fast  # go bigger
```

## Common patterns

### Process ensemble

Model N processes with per-process state via dicts:

```specl
var state: Dict[Int, Int]
init { state = {i: 0 for i in 0..N} }
action Transition(p: 0..N) { state = state | {p: newVal} }
```

### Message passing

Encode messages as sequences (fields packed into a tuple), store in a set:

```specl
var msgs: Set[Seq[Int]]
init { msgs = {} }

// Message types: [1, src, dst, term] = RequestVote
action SendRequestVote(src: 0..N, dst: 0..N) {
    require role[src] == 1
    msgs = msgs union {[1, src, dst, currentTerm[src]]}
}

action ReceiveRequestVote(src: 0..N, dst: 0..N, term: Int) {
    require [1, src, dst, term] in msgs
    // Process request...
}
```

### Quorum checks

```specl
// Simple majority
len({i in 0..N if voted[i]}) * 2 > N + 1

// Byzantine quorum (N = 3f+1, need 2f+1)
len({i in 0..N if certified[i]}) >= (N * 2) / 3 + 1
```

### Encoding enums as integers

```specl
// 0=follower, 1=candidate, 2=leader
var role: Dict[Int, 0..2]
action BecomeCandidate(i: 0..N) { require role[i] == 0; role = role | {i: 1} }
```

### Nondeterministic choice

Use action parameters — the checker explores all possible values:

```specl
action ChooseValue(v: 0..MAX) {
    require chosen == -1
    chosen = v
}
```

### Bounding collections

Prevent state space explosion by bounding queues:

```specl
action Send(msg: Seq[Int]) {
    require len(msgs) < MAX_MSGS
    msgs = msgs union {msg}
}
```

## State space scaling

| Constant change | Typical growth |
|-----------------|---------------|
| N: 2 -> 3 | 10-100x |
| N: 3 -> 4 | 100-1000x |
| MaxRound: +1 | 5-50x |
| Values: +1 | 2-10x |

Use `specl estimate spec.specl -c N=3` to get a rough estimate before running the full check.
