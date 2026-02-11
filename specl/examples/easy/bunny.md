 A puzzle game that went viral on Hacker News in 2022. It's a graph-based planning problem with a small state space, making it suitable for model
   checking while still being tricky for humans.

  Rules

  - You have a graph of nodes connected by edges
  - Animals (dog, rabbits) occupy nodes and can move along edges
  - Some edges have guards: conditions that must be true for the edge to be traversable (e.g., "someone must be at node X")
  - Multiple animals can share a node
  - Goal: get the dog to the bone and all rabbits to the carrot

  Example Instance

  nodes: [A, B, C, D, E]

  edges:
    - [A, B]
    - [B, C]
    - [C, D, {guard: "someone_at_E"}]
    - [D, E]
    - [A, E]
    - [B, D, {guard: "someone_at_A"}]

  bone: D
  carrot: E

  initial:
    dog: A
    rabbit1: B
    rabbit2: C

  State space: positions of 3 animals on 5 nodes = 125 states max.

  Solution

  Initial: (dog=A, r1=B, r2=C)

  1. dog A→E     → (E, B, C)   # opens the C→D gate
  2. r2  C→D     → (E, B, D)   # guard satisfied: dog at E
  3. r2  D→E     → (E, B, E)
  4. dog E→D     → (D, B, E)   # dog reaches bone
  5. r1  B→A     → (D, A, E)
  6. r1  A→E     → (D, E, E)   # both rabbits at carrot - done!

  The key insight: the dog must visit E first to unlock C→D for rabbit2, then backtrack to D. The B→D shortcut is a red herring.

  __

  Now a harder one:

   # State space: 7^5 = 16,807 states

  nodes: [A, B, C, D, E, F, G]

  edges:
    - [A, B]
    - [B, C]
    - [C, D]
    - [D, E]
    - [E, F]
    - [F, G]
    # Shortcuts
    - [A, D, {guard: "someone_at_F"}]
    - [B, E, {guard: "someone_at_G"}]
    - [C, F, {guard: "someone_at_A AND someone_at_E"}]
    - [D, G, {guard: "someone_at_B"}]

  bone: G
  carrot: F

  initial:
    dog: A
    r1: B
    r2: C
    r3: D
    r4: E

  The graph is a line A-B-C-D-E-F-G with four guarded shortcuts. The AND guard on C→F creates a narrow window.

  Why it's hard for humans:
  - 5 agents to track mentally
  - The optimal path requires using C→F before the dog moves (dog at A satisfies half the guard)
  - Tempting to move the dog first, which closes the C→F shortcut permanently
  - Multiple shortcuts with interdependent guards

  Optimal solution: 8 moves (I won't spoil it unless you want)

  A brute-force BFS explores a few thousand states and finds it instantly. A human trying to hold 5-tuples in their head while reasoning about
  guard dependencies will struggle.