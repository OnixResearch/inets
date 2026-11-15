import InteractionNets.Wires
import InteractionNets.Nets
import InteractionNets.Confluence
import InteractionNets.Renaming
import InteractionNets.Concurrent
import InteractionNets.Loops
import InteractionNets.Reducer
import InteractionNets.Program
import InteractionNets.Fair
import InteractionNets.Time
import InteractionNets.Symmetry
import InteractionNets.Matchings
import InteractionNets.HashMap
import InteractionNets.Indexed
import InteractionNets.Lazy
import InteractionNets.Packed
import InteractionNets.Ordered
import InteractionNets.Trees
import InteractionNets.Counted
import InteractionNets.Names
import InteractionNets.Bits
import InteractionNets.RoundByRound
import InteractionNets.Examples
import InteractionNets.Addition
import InteractionNets.Arith.Correct
import InteractionNets.Arith.Solo
import InteractionNets.Arith.TwoThreads
import InteractionNets.Arith.Readers
import InteractionNets.Arith.ThreeThreads
import InteractionNets.Arith.RaceLast
import InteractionNets.Arith.FourThreads
import InteractionNets.Arith.ManyThreads
import InteractionNets.Arith.Rounds
import InteractionNets.Arith.SideBySide
import InteractionNets.Arith.TwoSums
import InteractionNets.Arith.Apart
import InteractionNets.Arith.Floor
import InteractionNets.Arith.Late
import InteractionNets.Arith.Census
import InteractionNets.Arith.AtRest
import InteractionNets.Arith.Lists
import InteractionNets.Arith.ListsAtRest
import InteractionNets.Arith.AnyNets
import InteractionNets.Plug
import InteractionNets.Arith.Compose
import InteractionNets.Arith.Expr
import InteractionNets.ReadBack
import InteractionNets.Arith.Run
import InteractionNets.Embed
import InteractionNets.Arith.Carry
import InteractionNets.Peano
import InteractionNets.Keeps
import InteractionNets.PeanoCopy
import InteractionNets.PeanoMul
import InteractionNets.PeanoProd
import InteractionNets.PeanoPow
import InteractionNets.PeanoFact
import InteractionNets.PeanoRec
import InteractionNets.PeanoRun
import InteractionNets.PeanoGExpr
import InteractionNets.PeanoConst
import InteractionNets.Union
import InteractionNets.UnionExamples
import InteractionNets.PeanoExpr
import InteractionNets.LongRun
import InteractionNets.Window
import InteractionNets.Measure

/-!
# Interaction nets

A self-contained Lean 4 formalisation (no Mathlib) of Lafont's interaction nets
and of their fundamental theorem: reduction is *strongly confluent*.  The only
imports are `Std.Data.HashMap` and `Std.Data.TreeMap`, which ship with Lean
and are used by the last reducer and by the memories of the program with
threads.

The development is in the modules under `InteractionNets/`, imported here
in an order in which each imports only earlier ones, so they read as one
text.
This file holds the overview.

Main results, for an arbitrary interaction system `sys`:

* `INet.Step.wf`             reduction preserves well-formedness of nets,
                             including that every wire leaving a port reaches
                             a second, different port (`Net.WF.end_conn`)
* `INet.Step.free`           reduction preserves the interface (free ports)
* `INet.Step.diamond`        the diamond property (strong confluence)
* `INet.confluence`          confluence, with matching step counts
* `INet.normal_form_unique`  normal forms are unique, and every reduction
                             reaching one has the same length
* `INet.reduction_bounded`   if some reduction of length `n` reaches a normal
                             form, every reduction has length at most `n` and
                             extends to that normal form

Wire history is unobservable.  `Net.ObsEq` relates two nets with the same
named live agents, the same free ports and the same pairing of ends by wires.

* `INet.Net.ObsEq.step`         bisimulation: between well-formed equivalent
                                nets, every step is matched by exactly one
                                step, with equivalent results
* `INet.Net.ObsEq.normal_form`  equivalent nets have equivalent normal forms,
                                reached in the same number of steps
* `INet.Net.ObsEq.bounded`      the reduction bound transfers as well
* `INet.Net.ObsEq.confluence`   reductions of two equivalent nets can be
                                completed to equivalent nets, by paths of
                                equal total length
* `INet.Net.WF.compact`, `INet.Net.compact_obs`, `INet.Net.compact_idem`
                                the compact form of a net (every wire a single
                                segment, nothing else) is well formed,
                                equivalent to the net, and compact
* `INet.Site.compact_fire`      compaction commutes with firing
* `INet.CStep.diamond`, `INet.cconfluence`, `INet.cnormal_form_unique`
                                strong confluence and its consequences for
                                reduction without history (`CStep`: fire,
                                then compact)

Wires after a firing.

* `INet.Site.paired_fire`, `INet.Site.paired_fire_ifc_ifc`,
  `INet.Site.paired_fire_ifc_new`, `INet.Site.paired_fire_new_new`
                                which ends are paired after a firing: a wire
                                away from the pair stays, and each wire of
                                the right-hand side joins or extends the
                                wires that arrived at its interface ports
* `INet.Site.fire_local`        firing is local: in a net without history
                                the pairing after a firing is the pairing
                                after the same firing in the neighbourhood of
                                the pair (`Net.nbhd`), plus the segments away
                                from the pair

Firing several active pairs at once.  `Indep` lists active pairs that share
no agent; `Net.fireAll` fires them simultaneously.

* `INet.Indep.fireSeq_eq`       firing them one after the other gives the
                                simultaneous firing
* `INet.Indep.fireSeq_perm`     so the order in which they are fired does
                                not matter
* `INet.Indep.fireAll_steps`    the simultaneous firing is a reduction with
                                one step per pair
* `INet.Indep.compact_fireAll`  compaction commutes with simultaneous firing

Names are arbitrary.  A `Renaming` of a net is a map of identifiers that
keeps the identifiers in use apart and reserved names out of use; `Net.map`
applies it.

* `INet.Renaming.wf_map`        a renamed net is well formed
* `INet.Site.map_fire`          firing commutes with renaming, up to the
                                extension `rechild` of the renaming to the
                                new agents
* `INet.Step.map`, `INet.Step.of_map`, `INet.Steps.map`
                                the steps of a renamed net are exactly the
                                renamed steps of the net
* `INet.Renaming.normal_form`   the normal form of a renamed net is a
                                renaming of the normal form, reached in the
                                same number of steps
* `INet.Net.Iso.symm`, `INet.Net.Iso.trans`
                                being a copy is symmetric and transitive
                                once the history of one net is discarded:
                                if `M` is a copy of `N` then `N` is a copy
                                of `M` without its history, by an inverse of
                                the renaming, and a copy of a copy of `N` is
                                a copy of `N` without its history
* `INet.Net.Copy.refl`, `INet.Net.Copy.symm`, `INet.Net.Copy.trans`
                                so on well-formed nets without history,
                                being a copy by some renaming is an
                                equivalence relation
* `INet.Rhs.Lafont.reach`, `INet.Rhs.Lafont.presented`
                                Lafont's symmetry condition is the one a
                                `System` asks for: a symmetry of a
                                right-hand side that exchanges the two
                                sides of the interface exchanges every
                                agent connected to the interface with a
                                different one, and back; so the right-hand
                                side is, up to the numbering of its agents,
                                its own mirror image, with those agents
                                owned by one side or the other and the rest
                                by neither
* `INet.Site.fire_renum`, `INet.CStep.renum`, `INet.CStep.renum_inv`,
  `INet.System.Renum.normal_form`
                                the numbering of the agents of a rule does
                                not matter: firing with a renumbered
                                right-hand side gives the same net with the
                                new agents renamed, so two systems whose
                                rules are renumberings of each other
                                simulate each other up to copies, and reach
                                normal forms that are copies of each other
                                in the same number of steps
* `INet.Rhs.Renum.symm`, `INet.Rhs.Renum.trans`, `INet.Rhs.Renum.common`,
  `INet.Rhs.Lafont.presented_unique`, `INet.System.common_normal_form`
                                renumbering is symmetric and transitive, so
                                two presentations of one right-hand side
                                are renumberings of each other, whatever
                                symmetry gave them their owners, and two
                                systems that present the same right-hand
                                sides reduce alike, up to names
* `INet.Net.WF.junk`, `INet.Net.junk_obs`, `INet.Net.Iso.not_symm`
                                a segment between unused names can be added
                                to a well-formed net and is not observed;
                                with it, a copy of a net whose agent has the
                                empty name has no copy back: without
                                discarding history, being a copy is not
                                symmetric
* `INet.Net.Iso.step`, `INet.Net.Iso.step_inv`, `INet.Net.Iso.normal_form`
                                the same up to wire history: nets that are
                                copies of each other up to names and history
                                (`Net.Iso`) simulate each other, and their
                                normal forms are copies of each other
* `INet.Renaming.compact_map`, `INet.CStep.map`
                                compaction commutes with renaming, and so
                                does reduction without history
* `INet.Renaming.relabel`       relabelling the numbers in identifiers by
                                any injective function is a renaming, so
                                renamings that reverse the order used to
                                name new agents are covered

Concurrent execution.  In `Conc` a firing is not atomic: a *claim* deletes
the two agents of an active pair of the net as written so far, and the new
agents and segments are then written one at a time, interleaved with the
claims and writes of other firings.

* `INet.Run.sequential`         every concurrent execution is a sequential
                                reduction with one step per claim
* `INet.Run.terminal`, `INet.Run.confluent`
                                an execution with nothing left to do has
                                written the normal form, and all such
                                executions agree on it and on the number of
                                claims
* `INet.Conc.persist`           a visible active pair stays visible until it
                                is claimed, whatever the other actions
* `INet.Run.flush`, `INet.Steps.run`, `INet.XSys.steps_run`
                                finitely many missing writes can always be
                                completed, so with finite rules every
                                sequential reduction is a concurrent
                                execution; the rules of an executable system
                                are finite

A machine with shared memory.  `Mach` is the memory and one private state
for each thread, and `MStep` is one action of one thread.  A thread reads an
agent, follows the wire that leaves its principal port one segment at a
time, and reads the agent at the other end.  It takes the two agents with
two compare-and-swaps, and gives the first back if it does not get the
second.  It then writes the right-hand side from a private list.  Every
action reads or writes a single cell, and threads are interleaved in any
order.

* `INet.MStep.sim`              an action of the machine is an action of
                                `Conc` on the state it stands for, or leaves
                                that state unchanged
* `INet.MRun.sequential`        every execution of the machine is a
                                sequential reduction with one step per claim
* `INet.MRun.final`, `INet.MRun.confluent`
                                whatever the schedule and the number of
                                threads, when every thread is idle and no
                                active pair is left the memory holds the
                                normal form, and the number of claims is the
                                length of every reduction to it
* `INet.Mach.settle`, `INet.Mach.fire`
                                a thread can always finish alone what it has
                                started, and an idle thread can fire any
                                active pair visible in memory, whatever the
                                other threads are in the middle of
* `INet.Steps.mrun`, `INet.MRun.complete`, `INet.XSys.mrun_complete`
                                with finite rules the machine can perform
                                every sequential reduction, and from every
                                state it can get into the normal form is
                                still within reach
* `INet.Arith.sum_machine`, `INet.Arith.sum_machine_complete`
                                addition on the machine: a schedule that
                                ends has made `m + 1` claims and left the
                                numeral `m + n`, no schedule makes more, and
                                every one can be continued to the end

The machine as a program.  `XMach` is the machine on finite data, with a
program for each thread: it keeps a private list of the agents it has yet
to try, reads the first, follows the wire from its principal port, takes
the pair if there is a rule for it, writes the right-hand side, and starts
again from a fresh copy of the list of agents; when its list is empty it
rests.  `XMach.exec` runs the threads in the order given by a schedule and
counts the claims.

* `INet.XMach.act_sim`, `INet.XMach.exec_run`
                                an action of the program is an action of the
                                machine or changes nothing, so a run under
                                any schedule is an execution of the machine
* `INet.XMach.exec_agrees`, `INet.XMach.exec_le`
                                a run that ends with every thread idle after
                                as many claims as the list reducer took
                                steps has the reducer's result in memory,
                                once its history is forgotten; no run makes
                                more claims
* `INet.Comb.xgg2_exec`         two threads taking turns on two active
                                pairs: each makes one claim, and the result
                                is the list reducer's
* `INet.Arith.sum_exec`         a run on the net for `m + n` that ends idle
                                after `m + 1` claims leaves the numeral
                                `m + n`; evaluated for `1 + 1` on two
                                threads and `2 + 3` on three
* `INet.XMach.solo_complete`, `INet.XMach.solo_agrees`
                                one thread alone ends: on a net that has a
                                normal form it makes the claims of the
                                sequential reduction, leaves the normal form
                                in memory and rests; so it computes what the
                                list reducer computes, in as many claims
* `INet.Arith.sum_solo`         one thread alone adds `m` and `n` in `m + 1`
                                claims
* `INet.Turn.exists`, `INet.Turn.exec`, `INet.Turn.sequence`
                                a turn is one attempt of one thread while
                                the others wait; every thread can always
                                take one, it is a run of the program, and
                                turns can be taken in any order
* `INet.XMach.turns_complete`   threads that take turns finish: in any
                                sequence of turns in which every thread
                                keeps getting turns, from some turn on every
                                thread rests with an empty list, the claims
                                are those of the sequential reduction, and
                                the memory holds the normal form
* `INet.Arith.sum_turns`        addition by any number of threads that take
                                turns
* `INet.XMach.step_live`, `INet.XMach.Live.rest`
                                under every schedule, some thread answers
                                for each active pair that has a rule, so the
                                threads never all rest while one is left
* `INet.XMach.exec_rest`, `INet.XMach.exec_rest_agrees`
                                whatever the schedule, a run that ends with
                                every thread at rest has made the claims of
                                the sequential reduction and holds the
                                normal form, which is the list reducer's
                                result once the history is forgotten
* `INet.Arith.sum_rest`         addition under any schedule that ends at
                                rest
* `INet.Trail.fresh`, `INet.Trail.length_le`, `INet.XMach.Live.seek_bound`
                                a search is bounded under every schedule:
                                the ports a thread visits while following a
                                wire are pairwise distinct, so there are at
                                most as many as the goal has segments, plus
                                one
* `INet.XMach.step_progress`    every action is the action of a thread at
                                rest, a claim, or lowers a measure of what
                                the threads still have to do
* `INet.XMach.fair_complete`    under every fair schedule the run comes to
                                rest: if every thread keeps being scheduled,
                                however their actions overlap, then from
                                some action on every thread is idle with an
                                empty list, the claims are those of the
                                sequential reduction, and the memory holds
                                the normal form
* `INet.XMach.turns_bound`      a bound on the number of turns: if every
                                thread gets a turn in every window of `W`
                                turns, every thread rests with the normal
                                form after `W` times
                                `A + n * (A + C * n + 1) + 1` turns, for a
                                net with `A` agents, `n` steps and rules
                                that write at most `C` agents
* `INet.Arith.sum_turns_bound`  addition in a bounded number of turns, in
                                closed form
* `INet.Arith.sum_fair`         addition under any fair schedule
* `INet.trails_total`, `INet.Net.scan_le`
                                trails from different ends share no step, so
                                one pass of a thread over the agents takes
                                at most seven actions for each agent and one
                                for each segment, whatever the other threads
                                do meanwhile
* `INet.XMach.step_nodup`       no agent is ever in memory twice, if none
                                was at the start
* `INet.XMach.act_pot`, `INet.XMach.step_pot`
                                measured in the normal form, which lies
                                ahead of every goal, each thread has a share
                                of the work left that no other thread can
                                raise: an action of the thread is a rest, a
                                claim, or lowers it; a claim raises it by
                                one pass and the writes of one rule
* `INet.XMach.fair_bound`       a bound on the length of a fair run: if
                                every thread is scheduled in every window of
                                `F` actions, every thread is at rest with
                                the normal form after `F` times
                                `(n + 1) * pass + n * (C + D + 1) + 1`
                                actions, for `n` steps and rules that write
                                at most `C` agents and `D` segments, where
                                `pass` (`XNet.passBound`) is seven for each
                                agent and one for each segment the net can
                                come to have: for each thread one pass, one
                                more for each claim whoever makes it, and
                                the writes; the threads are not added up
* `INet.fair_window_le`         such a window has at least as many actions
                                as there are threads, which is the only way
                                their number enters the bound
* `INet.XMach.solo_bound`, `INet.XMach.roundRobin_bound`
                                the same for one thread alone and for
                                threads scheduled in turn
* `INet.Arith.sum_fair_bound`   addition in a bounded number of actions, in
                                closed form: the window times a polynomial
                                of degree two in `m` and `n`, whatever the
                                number of threads
* `INet.Works.trace`            a run of one thread counted action by
                                action: where it is after its actions, and
                                that it is not at rest before
* `INet.Eps.solo_exact`, `INet.Eps.solo_tight`, `INet.Eps.bound_le`
                                for one thread the bound is right up to a
                                constant: on a net with `k` agents on free
                                ports and `n` active pairs that leave
                                nothing, one thread takes
                                `(n + 1) * (3 * k) + 6 * n` actions exactly,
                                and the bound is
                                `(n + 1) * (9 * k + 16 * n) + n + 1`, at
                                most nine times as many when `n ≤ k`
* `INet.XMach.trace_reads`, `INet.XMach.starved`
                                threads that only read do not disturb each
                                other, so a thread that gets one action in
                                `F` at most and needs `k` of its own keeps
                                the program from rest for `F * k - F`
                                actions
* `INet.Eps.window_tight`       the window must multiply the work of a
                                thread: on a net in normal form with `k`
                                agents on free ports one thread is at rest
                                after `3 * k` actions, two threads under a
                                fair schedule with window `F` are not at
                                rest after `F * (3 * k) - F`, and the bound
                                for them is `F * (9 * k + 1)`, about three
                                times as many
* `INet.Eps.window_many`        the same for any number of threads that the
                                window has room for
* `INet.XMach.trace_lone`, `INet.XMach.starved_worker`
                                with the other threads at rest the program
                                is where one thread's own actions take it,
                                so a thread that gets one action in `F` at
                                most and has `k` to make keeps the program
                                from rest for `F * k - F` actions
* `INet.Chain.solo_exact`       a chain of pairs in which each firing joins
                                the next pair through the ports of the pair
                                that is gone: one thread fires `n + 1` pairs
                                behind `k` agents that lead nowhere in
                                `3 * k + 8 + (n + 1) * (3 * k) + 10 * n`
                                actions, exactly
* `INet.Chain.window_chain`     the window multiplies every pass: with two
                                threads and a window `F` longer than
                                `3 * k + 6 * n + 8`, there is a fair
                                schedule under which the starved thread
                                fires every pair but the first; the bound
                                is `F` times
                                `(n + 2) * (11 * k + 20 * n + 33) + 3 * n + 4`
                                and the threads are not at rest after `F`
                                times `(n + 1) * (3 * (k + 1)) + 10 * n + 3`,
                                less `F`
* `INet.XMach.trace_quiet`, `INet.XMach.trace_turns`
                                threads that only read for a while do not
                                disturb each other meanwhile, so two threads
                                that take turns can be followed one by one
                                up to the first write
* `INet.abreast_fair`           the schedule that gives two threads an
                                action each in turn and then starves the
                                second is fair with any window of two
                                actions or more
* `INet.Chain.ropening`         on the chain listed from the last pair to
                                the first, two threads in turn reach the
                                first pair three actions apart: the one
                                ahead takes it, and the other, which has
                                passed every other pair, finds it gone and
                                rests
* `INet.Chain.window_short`     the window multiplies every pass, however
                                short it is: on that net, for every window
                                `F` of two actions or more, there is a fair
                                schedule under which the starved thread
                                fires every pair; the bound is the same,
                                and the threads are not at rest after `F`
                                times
                                `(n + 1) * (3 * (k + 1)) + 3 * (n * n) + 7 * n + 3`,
                                less `F`
* `INet.Chain.short_bound_le`   on that net the bound is at most twelve
                                times that count, so it is right up to a
                                constant for every window
* `INet.assoc_take`, `INet.nextSeg_take`
                                a lookup in a list depends only on the cells
                                up to the entry it finds, which is what it
                                is charged for
* `INet.XMach.cost_le`          an action costs at most twice the agents in
                                memory, the segments, and the size of a rule
* `INet.XMach.step_work`        every action is free and changes nothing,
                                or is a claim, or lowers the sum of the
                                shares of the threads
* `INet.XMach.time_bound`       a bound on the running time, in list cells
                                read, whatever the schedule, fair or not:
                                `(nt + n) * pass + n * (C + D + 1)` actions
                                that are not rests, times the most an
                                action can cost in a memory that never
                                holds more than the net and `n` right-hand
                                sides; a window stretches the run, not the
                                work
* `INet.Arith.sum_time`         addition in bounded time, in closed form
* `INet.XMach.time_reads`, `INet.XMach.time_ge_rest`
                                the time of threads that only read is what
                                each spends on its own, added up; at rest
                                each has paid for its whole pass
* `INet.Eps.time_tight`, `INet.Eps.time_bound_le`
                                the bound on the time is right up to a
                                constant: on `k` agents on free ports with
                                nothing to reduce, any number of threads
                                under any schedule have taken
                                `nt * (k * (3 * k + 3))` or more when they
                                are at rest, and the bound is
                                `nt * (9 * k) * (4 * k + 1)`, at most twelve
                                times as much
* `INet.XMach.time_lone`        the time of one thread at work, the others
                                at rest, is the time of its own actions
* `INet.Chain.time_chain`, `INet.Chain.time_chain_le`
                                the same with claims: one thread on the
                                chain listed from the last pair reads the
                                whole memory again after every firing, for
                                each agent that leads nowhere, and every
                                segment for each agent of a pair still to
                                come; with at least one agent that leads
                                nowhere the bound is at most 168 times the
                                time it takes

The program on an indexed memory.  `IMem` keeps the agents in a log, each
cell with a stamp, with a hash map from the names of the agents to the
cells that are live, and the segments in a list with a hash map from each
port to its neighbours.  `IMach` is the program with threads on that
memory: every lookup is one operation on a map.

* `INet.IMem.Ok.sym`, `INet.IMem.Ok.first`, `INet.IMem.Ok.next`
                                a lookup in a map returns what the lookup
                                in the list returns, for the agents, for
                                the first neighbour of a port and for the
                                next one
* `INet.findCells_nbOf`         a search among the neighbours of a port
                                reads two cells at most
* `INet.IMem.toX_take`, `INet.IMem.toX_put`, `INet.IMem.toX_pack`
                                erasing a name takes the agent out of the
                                list, cell for cell; writing an agent that
                                is not in memory puts it at the front;
                                packing the log changes nothing
* `INet.IMem.ofX_toX`           the indexed memory of a net in which no
                                agent is listed twice stands for the net
* `INet.IMach.act_sim`          one action on the indexed memory does to
                                the lists it stands for what the action of
                                the program does, leaves the thread in the
                                same state, claims as often, and keeps the
                                maps right
* `INet.IMach.init_sim`         so under any schedule, after any number of
                                actions, the indexed program stands for the
                                state of the program on lists
* `INet.IMach.fair_complete`, `INet.IMach.fair_bound`
                                under a fair schedule it comes to rest with
                                the normal form, within the same number of
                                actions
* `INet.XMach.work_measure`     there is a measure, at most
                                `(nt + n) * pass + n * (C + D + 1)` at the
                                start, that every action but a rest brings
                                down
* `INet.XMach.packs_le_claims`  a thread takes the list of agents afresh
                                only after a claim of its own
* `INet.IMach.cost_le`          on the indexed memory an action costs the
                                size of a rule and seven at most, whatever
                                the size of the memory, and adds one cell
                                to the log at most; taking the agents
                                afresh costs the log and leaves it with the
                                agents only
* `INet.IMach.time_bound`       the running time, in operations on the
                                maps, whatever the schedule: the actions
                                that are not rests times `C + D + 7`, and
                                `(2 * n + 1) * (agents + C * n)` for taking
                                the agents afresh
* `INet.Arith.sum_itime`        addition on the indexed memory in bounded
                                time, in closed form
* `INet.IMach.cost_le_list`, `INet.IMach.time_le_list`
                                run for run, the time on the indexed memory
                                is at most the agents of the net and
                                `C + D + 9` times the time on lists: the
                                index never loses by more than a constant
* `INet.XMach.tally_reads`, `INet.IMach.time_ge_least`
                                for threads that only read, a run comes to
                                what each thread comes to on its own, at
                                any rate for each state; the indexed time
                                is at least what the actions come to at
                                their least cost
* `INet.Eps.itime_tight`, `INet.Eps.itime_bound_le`
                                on `k` agents on free ports the indexed
                                bound is `nt * (63 * k) + k` and the run
                                has taken `nt * (7 * k)` or more at rest:
                                right up to a factor of ten, and linear
                                where lists are quadratic
* `INet.Eps.index_gain`         there, at rest, lists have taken
                                `(3 * k + 3) / 64` times as long as the
                                index, or more, for any threads and any
                                schedule
* `INet.Chain.itime_chain`, `INet.Chain.index_gain`
                                with claims: for one thread on the chain
                                listed from the last pair, lists have
                                taken `(6 * k + 10 * n + 15) / 1680` times
                                as long, or more
* `INet.XMach.work_le`          the actions that are not rests number at
                                most `(nt + n) * pass + n * (C + D + 1)`,
                                whatever the schedule
* `INet.IMach.time_ge_work`, `INet.IMach.time_le_work`
                                the indexed time is the work up to a
                                constant: at least twice the actions that
                                are not rests, less one for each claim,
                                and at most `C + D + 7` for each, the
                                agents of the net, and twice the agents
                                the memory can hold for each claim
* `INet.Chain.work_chain`, `INet.Chain.work_bound_le`
                                one thread on the chain listed from the
                                last pair makes exactly
                                `3 * k + 6 * n + 8 + (n + 1) * (3 * k) +
                                3 * (n * n) + 7 * n` actions that are not
                                rests, and the bound on the work is at
                                most seven times that
* `INet.Chain.itime_ge`, `INet.Chain.itime_chain_le`
                                so the indexed time of that run is
                                `(n + 2) * (6 * k) + 6 * (n * n) + 25 * n +
                                15` or more, and the indexed bound is at
                                most thirty-one times that: right up to a
                                constant with claims as well
* `INet.IMach.time_shadow`      the indexed time, the length of the log and
                                the part of the time that goes to taking
                                the agents afresh are what a function on
                                lists computes along the run of the
                                program on lists; hashing does not enter,
                                so the kernel can evaluate them
* `INet.Arith.sum23_itime`, `INet.Arith.sum23_work`
                                `2 + 3` on three threads scheduled in turn
                                takes 420 on the indexed memory, where it
                                takes 1,213 on lists; 107 actions are not
                                rests, and 53 of the 420 go to taking the
                                agents afresh
* `INet.Arith.sum12_time`, `INet.Arith.sum12_itime`, `INet.Arith.sum12_work`
                                `12 + 12` on one thread takes 10,514 on
                                lists and 2,028 on the indexed memory, in
                                313 actions; 737 of the 2,028 go to taking
                                the agents afresh, thirteen times

The program with lazy lists.  `LMach` is the indexed program without the
packing.  A thread that has written a right-hand side takes the log as it
stands, with the time, and reads none of it.  A third hash map says when
each dead cell died, and an idle thread drops the cells at the front of
its list that were dead when it took the list.

* `INet.LMem.seen_take`, `INet.LMem.seen_now`
                                a death noted now does not change what an
                                earlier clock saw, and what the clock sees
                                now is what is live
* `INet.LMach.act_sim`, `INet.LMach.init_sim`
                                action by action, under any schedule, the
                                lazy program stands for the program on
                                lists and claims as often; the other
                                threads stand for what they stood for
* `INet.LMach.fair_complete`, `INet.LMach.fair_bound`
                                under a fair schedule it comes to rest with
                                the normal form, within the same number of
                                actions
* `INet.LMach.cost_fresh`, `INet.LMach.cost_le`
                                taking the agents afresh costs one; an
                                action that is not a rest costs at most
                                `C + D + 8`, and two for each dead cell an
                                idle thread drops
* `INet.LMach.time_le_work`     so on every run the time is at most
                                `C + D + 8` for each action that is not a
                                rest and two for each dead cell dropped; no
                                normal form is needed
* `INet.LMach.time_shadow`      the time, the dead cells dropped and the
                                marks of the log and of the threads are
                                what a function on lists computes along
                                the run of the program on lists, so the
                                kernel can evaluate them
* `INet.Arith.sum12_ltime`, `INet.Arith.sum12_lskips`, `INet.Arith.sum23_ltime`
                                `12 + 12` on one thread takes 1,394 with
                                lazy lists, where the indexed memory takes
                                2,028 and lists 10,514, and drops 26 dead
                                cells; `2 + 3` on three threads scheduled
                                in turn takes 407

The packing memory.  `PMach` is the program with lazy lists on a memory
that counts its live cells and the length of its log, and drops the dead
cells of the log as soon as they are more than half of it.  The threads
keep the lists they took.

* `INet.PMach.act_sim`, `INet.PMach.init_sim`
                                action by action, under any schedule, the
                                program on the packing memory stands for
                                the program on lists and claims as often
* `INet.PMach.fair_complete`, `INet.PMach.fair_bound`
                                under a fair schedule it comes to rest with
                                the normal form, within the same number of
                                actions
* `INet.PMach.log_le`           at every action of every run the log is at
                                most twice the agents in memory
* `INet.PMach.cost_le`, `INet.PMach.time_le_work`
                                packing pays for itself: with three counted
                                for every dead cell in the log, an action
                                costs at most `C + D + 11` and two for each
                                dead cell dropped, so the time of a run is
                                at most that for each action that is not a
                                rest and two for each dead cell dropped
* `INet.PMach.act_stale`, `INet.PMach.skips_le`
                                a thread drops only cells that were dead
                                when it took its list, at most as many as
                                the live cells of that moment; the threads
                                drop at most `n * (agents + C * n)` in all
* `INet.PMach.time_bound`       the running time, whatever the schedule:
                                the actions that are not rests times
                                `C + D + 11`, and `2 * n * (agents + C * n)`
                                for the dead cells dropped
* `INet.PMach.time_shadow`      the time on the packing memory is what a
                                function on lists computes along the run of
                                the program on lists
* `INet.Arith.sum12_ptime`, `INet.Arith.sum12_pskips`, `INet.Arith.sum23_ptime`
                                `12 + 12` on one thread takes 1,444 on the
                                packing memory, drops no dead cell and ends
                                with a log of the 25 live cells; `2 + 3` on
                                three threads scheduled in turn takes 407

The ordered memory.  `TMach` keeps the agents in a persistent map ordered
by stamp, the live ones only.  A copy of the map is the list of the agents
as it stands, so a thread takes the agents afresh by keeping the map it
finds, and works through its own copy from the largest key down.  Nothing
is marked dead, dropped or packed.

* `INet.sorted_ext`, `INet.toList_insert_max`, `INet.toList_erase`,
  `INet.toList_max`             lists that go up in their keys are the same
                                when they have the same entries; so
                                inserting above every key adds at the end
                                of the list of the map, erasing takes one
                                entry out, and the largest key is the last
* `INet.TMem.Ok.sym`, `INet.TMem.take_spec`, `INet.TMem.toX_put`,
  `INet.TMem.ofX_toX`           the lookups and the changes of the ordered
                                memory are those of the lists it stands
                                for
* `INet.TMach.act_sim`, `INet.TMach.init_sim`
                                action by action, under any schedule, the
                                program on the ordered memory stands for
                                the program on lists and claims as often
* `INet.TMach.fair_complete`, `INet.TMach.fair_bound`
                                under a fair schedule it comes to rest with
                                the normal form, within the same number of
                                actions
* `INet.XMach.tcost_le`, `INet.TMach.time_le_work`, `INet.TMach.time_bound`
                                every action costs at most `C + D + 6`, so
                                the time of a run is at most that for each
                                action that is not a rest, and nothing
                                else; with the bound on those actions, a
                                bound on the running time for every
                                schedule
* `INet.TMach.time_eq`          the time is what a function on lists
                                computes along the run of the program on
                                lists, with no further state
* `INet.TMach.cells_size`, `INet.TMach.todo_le`
                                the memory holds one cell for each agent,
                                and no thread holds more than
                                `agents + C * n`
* `INet.Arith.sum12_ttime`, `INet.Arith.sum23_ttime`
                                `12 + 12` on one thread takes 1,444 on the
                                ordered memory, and `2 + 3` on three
                                threads scheduled in turn takes 451

The ordered memory, the depth of the map charged.  `lg n` is one more than
the number of binary digits of `n`.  `TMach.lgtime` counts the time on the
ordered memory with each operation on an ordered map of `n` entries
charged `lg n`; an operation on a hash map still counts one.

* `INet.lg_le`, `INet.lt_pow_lg`, `INet.lg_mono`
                                a map of fewer than `2 ^ k` entries is
                                charged `k + 1` at most, `2 ^ lg n`
                                exceeds `2 * n`, and a larger map is
                                charged no less
* `INet.XMach.lgcost_le`, `INet.TMach.lgtime_le_work`,
  `INet.TMach.lgtime_bound`     every action costs at most
                                `C + D + 3 + 3 * lg m` when no map has
                                more than `m` entries, so the time of a
                                run is at most
                                `C + D + 3 + 3 * lg (agents + C * n)` for
                                each action that is not a rest; with the
                                bound on those actions, a bound on the
                                running time for every schedule
* `INet.TMach.time_le_lgtime`, `INet.TMach.lgtime_le_time`
                                charging the depth never lowers the time,
                                and multiplies it by
                                `lg (agents + C * n)` at most
* `INet.TMach.lgtime_eq`        this time too is what a function on lists
                                computes along the run of the program on
                                lists
* `INet.Arith.sum12_lgtime`, `INet.Arith.sum23_lgtime`
                                with the depth charged, `12 + 12` on one
                                thread takes 2,186 and `2 + 3` on three
                                threads scheduled in turn takes 688

The depth of the trees of the library.  `tdepth t` is the depth of the
tree that the map `t` of `Std.TreeMap` is kept in, and `TMach.dtime`
charges each operation on an ordered map that depth and one.

* `INet.implDepth_pow`, `INet.tdepth_lt`, `INet.lg_le_tdepth`
                                a tree of the library of `n` entries and
                                depth `d` has `(4 / 3) ^ d ≤ n + 1`, so
                                `d < 3 * lg n`; and `lg n ≤ d + 1`
* `INet.TMach.lgtime_le_dtime`, `INet.TMach.dtime_le_lgtime`
                                on every run from every state, the time
                                by the depth is between the time by `lg`
                                and three times it
* `INet.TMach.dcost_le`, `INet.TMach.dtime_le_work`,
  `INet.TMach.dtime_bound`      every action costs at most
                                `C + D + 3 + 9 * lg (agents + C * n)`,
                                and with the bound on the actions that are
                                not rests, a bound on the running time for
                                every schedule
* `INet.TMach.act_strip`, `INet.TMach.trace_strip`,
  `INet.TMach.dtime_replay`     a replay without the hash maps, which
                                finds an agent by going through the map
                                of the agents, keeps the trees of the run
                                action by action; so the time by the depth
                                is the time of the replay, and the kernel
                                computes that
* `INet.Arith.sum12_dtime`, `INet.Arith.sum23_dtime`
                                by the depth, `12 + 12` on one thread
                                takes 2,240 and `2 + 3` on three threads
                                scheduled in turn takes 692

The steps of the operations on the trees.  Each operation the program
makes on an ordered map is written again with a counter of its calls: the
lookup, the search for the largest key, the insertion and the erasure.  A
call makes one comparison at most and one call of a balancing function of
the library, which is not recursive.

* `INet.tgetC_fst`, `INet.tmaxC_fst`, `INet.tinsertC_fst`,
  `INet.teraseC_fst`            the counted operations return what the
                                operations of `Std.TreeMap` return
* `INet.tgetC_snd`, `INet.tmaxC_snd`, `INet.tinsertC_snd`,
  `INet.teraseC_snd`, `INet.tsteps_le_lg`
                                each makes at most one call for each level
                                of the tree, and one; so at most
                                `3 * lg n` on a map of `n` entries
* `INet.TMach.ctime_le_dtime`, `INet.TMach.ctime_bound`
                                the running time with those calls counted
                                is at most the time by the depth, on every
                                run; so it is bounded for every schedule
* `INet.TMach.ctime_replay`     and it is the time of the replay
* `INet.Arith.sum12_ctime`, `INet.Arith.sum23_ctime`
                                with the calls counted, `12 + 12` on one
                                thread takes 2,007 and `2 + 3` on three
                                threads scheduled in turn takes 573

Ordered maps alone.  `OMach` keeps the names of the agents and the
neighbours of the ports in ordered maps too, keyed by names in the order
of lists of numbers, so that no operation is counted one on the strength
of a hash.

* `INet.OMach.act_agree`, `INet.OMach.trace_agree`, `INet.OMach.init_sim`
                                action by action, under any schedule, the
                                program on ordered maps alone does what
                                the program on the ordered memory does;
                                so it stands for the program on lists and
                                claims as often
* `INet.OMach.fair_complete`, `INet.OMach.fair_bound`
                                under a fair schedule it comes to rest with
                                the normal form, within the same number of
                                actions
* `INet.OMem.Sized`, `INet.OMach.trace_sized`, `INet.XMach.wires_le`
                                the map of the names is no larger than the
                                map of the agents, the map of the
                                neighbours has no more keys than there are
                                segments, and the segments are at most
                                those of the net and `D` for each
                                interaction
* `INet.OMach.ccost_le`, `INet.OMach.ctime_le_work`,
  `INet.OMach.ctime_bound`      with every call on every map counted, an
                                action costs at most `C + D + 4 + 12 * lg m`,
                                where `m` is what the memory can hold,
                                agents and segments together; with the
                                bound on the actions that are not rests, a
                                bound on the running time for every
                                schedule
* `INet.Arith.sum12_otime`, `INet.Arith.sum23_otime`
                                so counted, `12 + 12` on one thread takes
                                4,343 and `2 + 3` on three threads
                                scheduled in turn takes 948

Everything counted.  `OMach.ftime` charges an operation on a map every
call it makes, every cell that a comparison of two keys reads, and every
node it builds, the balancing included.

* `INet.balanceLF_fst`, `INet.balanceRF_fst`, `INet.balanceLF_snd`,
  `INet.balanceRF_snd`          the balancing functions of the library,
                                written again with the nodes they build,
                                return what the library returns and build
                                three nodes at most
* `INet.cmpC_fst`, `INet.cmpC_snd`
                                the comparison of two names, written again
                                with the cells it reads, is the comparison
                                of the library, and reads at most the
                                cells of the first name and one
* `INet.tgetF_snd`, `INet.tinsertF_snd`, `INet.teraseF_snd`,
  `INet.ngetF_snd`, `INet.ninsertF_snd`, `INet.neraseF_snd`
                                an operation costs at most five for each
                                level of the tree on numbers, and the
                                length of the name and five on names
* `INet.XMach.act_names`, `INet.XMach.names_le`
                                an action lengthens the names by one cell
                                at most, and only when it claims; so no
                                name grows beyond the longest of the net
                                by more cells than there are interactions
* `INet.OMach.fcost_le`, `INet.OMach.ftime_le_work`,
  `INet.OMach.ftime_bound`      everything counted, an action costs at
                                most `C + D + 4 + 12 * (L + n + 6) * lg m`
                                when no name of the net has more than `L`
                                cells; with the bound on the actions that
                                are not rests, a bound on the running time
                                for every schedule
* `INet.Arith.sum12_ftime`, `INet.Arith.sum23_ftime`
                                so counted, `12 + 12` on one thread takes
                                11,902 and `2 + 3` on three threads
                                scheduled in turn takes 2,195

New names.  The names a claim gives to the agents it creates are new to
the whole state of the program.

* `INet.XMach.act_wired`, `INet.XMach.trace_wired`
                                every name in the list or the hand of a
                                thread is an agent of the memory or lies
                                on one of its segments, at every moment of
                                every run
* `INet.XMach.claim_fresh`, `INet.XMach.fresh_names`
                                when a thread holds an agent and finds its
                                partner, no name of an agent that the rule
                                creates occurs anywhere: not as an agent,
                                not on a segment, not in the list or the
                                hand of any thread, not among the agents
                                and segments still to be written
* `INet.XMach.act_map`          an action does not depend on the names:
                                on a memory and a thread renamed by a map
                                that keeps the names they hold apart, it
                                leaves the renamed memory and claims as
                                before, and unless it claims it leaves the
                                renamed thread

Numbered names.  The program that names each new agent by a number: it
does what the program with long names does, and its names stay short.

* `INet.YMach.act`, `INet.YMach.step`, `INet.YMach.init`
                                the program on lists with a counter: a
                                claim names the agents it creates by the
                                next numbers, and nothing else changes
* `INet.XRhs.newAgents_num`, `INet.XRhs.newLinks_num`
                                the agents and segments that a claim
                                writes are those of the numbered claim,
                                renamed
* `INet.XMach.child_fresh`      when a thread holds an agent and finds its
                                partner, no name that a child of the two
                                could bear occurs anywhere in the state
* `INet.YMach.step_rel`, `INet.YMach.trace_rel`
                                at every moment of every run, under any
                                schedule, the state of the named program
                                is the state of the numbered one renamed,
                                by a renaming that keeps its names apart,
                                and both have claimed as often
* `INet.YMach.fair_complete`    under a fair schedule the numbered program
                                comes to rest, having claimed once for
                                each step to the normal form, with a
                                memory that is the normal form up to the
                                names
* `INet.YMach.names_le`         no name of the numbered program is ever
                                longer than the longest name of the net,
                                or than one cell
* `INet.ZMach.act`, `INet.ZMach.init`
                                the numbered program on ordered maps
                                alone
* `INet.ZMach.trace_sim`, `INet.ZMach.trace_rel`
                                it runs as the numbered program on lists
                                does, so its state renamed is the state
                                of the named program at every moment of
                                every run
* `INet.ZMach.fair_complete`    under a fair schedule it comes to rest
                                with the normal form, up to the names
* `INet.ZMach.fcost_le`, `INet.ZMach.ftime_le_work`,
  `INet.ZMach.ftime_bound`      everything counted, an action costs at
                                most `C + D + 5 + 12 * (max L 1 + 6) * lg m`:
                                the length of the run is no longer in the
                                cost of an action; with the bound on the
                                actions that are not rests, a bound on
                                the running time for every schedule
* `INet.Arith.sum12_ztime`, `INet.Arith.sum23_ztime`
                                so counted, `12 + 12` on one thread takes
                                10,999 and `2 + 3` on three threads
                                scheduled in turn takes 2,126
* `INet.YMach.cnt_le`, `INet.YMach.cells_lt`
                                the counter never passes `X.top + Sp * n`,
                                with `Sp` the largest span of a rule, and
                                every cell of every name is below that
                                bound, at every moment of every run
* `INet.ZMach.stamp_le`         the stamps stay below the agents of the
                                net plus the bound on the actions that
                                are not rests
* `INet.ZMach.numbers_lt`       so every number the numbered program
                                holds, the counter, the cells of the
                                names and the stamps, fits in a word
                                whose size is fixed before the run
* `INet.Arith.sum12_numbers`    on `12 + 12` the counter ends at 64, under
                                its bound of 67, and the next stamp at 51
* `INet.cellBits`, `INet.cmpB`, `INet.nameBits`
                                the bits read to compare two numbers,
                                those of the shorter; the bits read to
                                compare two names; the size of a name in
                                bits
* `INet.ngetB_le`, `INet.tgetB_le`, and the same for insertions and
  erasures                      in bits, an operation on a map costs at
                                most its count times the bits of its key
* `INet.ZMach.bcost`, `INet.ZMach.btime`
                                the time of the numbered program in bits:
                                every comparison of two numbers and every
                                number made is charged its bits
* `INet.Arith.sum12_btime`, `INet.Arith.sum23_btime`
                                in bits, `12 + 12` on one thread takes
                                28,984 and `2 + 3` on three threads
                                scheduled in turn takes 4,220
* `INet.YMach.ports_le`         the indices of the ports do not grow: none
                                is above a bound on those of the net and
                                of the rules
* `INet.ZMach.bcost_le`         in bits, an action costs at most three
                                times its count times the bits of a key
* `INet.ZMach.btime_le_ftime`, `INet.ZMach.btime_bound`
                                the time in bits is at most
                                `3 * (lg P + max L 1 * (W + 1) + 1)` times
                                the count, at every moment of every run;
                                with the bound on the count, a bound on
                                the running time in bits for every
                                schedule
* `INet.Arith.xsys_ports`, `INet.Arith.sum12_ports`
                                for addition, no port of a rule or of
                                `12 + 12` has an index above two
* `INet.Arith.sum_ztime`, `INet.Arith.sum_btime`
                                addition of any two numbers, numbered, on
                                any number of threads and whatever the
                                schedule: a closed bound on the count and
                                a closed bound on the bits
* `INet.Arith.solo_work_checked`
                                on one thread, for all `m` and `n` below
                                nine, the run for `m + n` rests after
                                exactly `22 * m + 3 * n + 13` actions, none
                                of them a rest: a computation, size by
                                size
* `INet.Arith.ztime_of_work`, `INet.Arith.btime_of_work`,
  `INet.Arith.sum12_solo`       a run whose work is known is bounded by
                                it, counted and in bits: 267,615 and
                                16,056,900 for `12 + 12` on one thread

One thread.  A run of a single thread is a sequence of rounds, each a
fresh start on the memory left by the last.

* `INet.XMach.work_add`         the work of a run is the work up to a cut
                                and the work after it
* `INet.XMach.single_write`, `INet.XMach.single_claim`
                                from a claim, the single thread writes the
                                right-hand side in one action for each
                                agent and segment and two more, and is
                                then the program started on the memory as
                                it is
* `INet.XMach.restart`          from there the run is the run on that
                                memory, and the claims and the work add up
* `INet.Works.work`, `INet.Works.write`
                                a counted run without rests is all work;
                                the writes of a claim as a counted run
* `INet.Works.claim_direct`, `INet.Works.claim_via`
                                a whole round, counted: the thread takes
                                the first agent of its list, finds the
                                partner on the next segment or one point
                                further, claims, writes, and is idle with
                                every agent of the new memory in its
                                list, in five or six actions and the
                                writes
* `INet.Arith.Start.round`, `INet.Arith.Steady.round`
                                the rounds of an addition on a net of any
                                size: the first in sixteen actions, each
                                later one in seventeen, and the memory is
                                ready for the next
* `INet.Arith.start_sum`        the net for `(m + 1) + n` is ready for the
                                first round
* `INet.Arith.solo_work_le`     one thread adds `m` and `n` in at most
                                `83 * m + 22 * n + 152` actions, for every
                                `m` and `n`
* `INet.Arith.solo_ztime_le`, `INet.Arith.solo_btime_le`
                                so its count and its bits are bounded by
                                that many times the cost of an action
* `INet.XNet.Dead`, `INet.Stays.dead`
                                a walk of a thread that ends nowhere, with
                                its exact length: the entry costs two
                                actions and one for each point passed
* `INet.Arith.Hist`, `INet.Arith.Final`, `INet.Arith.solo_rounds`
                                the memory through the rounds of an
                                addition, exactly: the agents in order,
                                and every segment, those of the net and
                                those each round wrote
* `INet.Arith.Final.pass`       the last pass, entry by entry: four
                                actions for each successor of the result,
                                `m + 5` for the top of the second
                                argument, three for each entry below it
* `INet.Arith.solo_work`        one thread adds `m` and `n` in exactly
                                `22 * m + 3 * n + 13` actions, for every
                                `m` and `n` (`6 * n + 13` when `m` is
                                zero): at rest then and not before, and no
                                action a rest
* `INet.XThread.opsA`, `INet.XThread.opsW`, `INet.Opers`
                                the operations that an action is charged,
                                by the state of the thread, on the maps of
                                agents and on the map of segments, and
                                counted runs that carry them
* `INet.ZMach.ftime_le_ops`     the count of the numbered program is at
                                most the size of a rule and five for each
                                action, and for each operation charged the
                                cost of one on its own tree at full depth
* `INet.ZMach.work_le_ftime`    and it is at least one for each action
                                that is not a rest
* `INet.Arith.solo_ops`         one thread adds `m` and `n` charged
                                `23 * m + 5 * n + 18` operations on the
                                maps of agents and `23 * m + 2 * n + 10`
                                on the map of segments, for every `m` and
                                `n` (`10 * n + 18` and `4 * n + 10` when
                                `m` is zero)
* `INet.Arith.solo_ztime_ops`, `INet.Arith.solo_ztime_ge`,
  `INet.Arith.solo_btime_ops`   so its count is at most fifteen for each
                                action, `18 * lg` of the agents for each
                                operation on their maps and `21 * lg` of
                                the segments for each on theirs, and at
                                least its work, for every size; and its
                                bits are bounded with the count

Two threads.  A second thread can make the program slower.

* `INet.blockSched`, `INet.BlockRun`, `INet.BlockRun.work`
                                a schedule given by blocks, each a counted
                                run of one thread while the others wait:
                                such a run is all work
* `INet.Arith.Steady.round_swap`, `INet.Arith.stepS_agents`,
  `INet.Arith.stepS_wires`      a round of an addition claimed from the
                                side of the successor, and the memory it
                                leaves, which is that of the round claimed
                                from the adder
* `INet.Arith.alt_block`, `INet.Arith.alt_run`
                                two threads that claim in turn on an
                                addition, each running alone until its
                                claim is written: the thread that holds
                                the older list passes every successor of
                                the result that it lists before it claims
                                the next pair
* `INet.Arith.two_threads_quadratic`, `INet.Arith.two_threads_any`
                                so under that schedule the first
                                `2 * m * m + 21 * m + 33` actions on the
                                net for `(m + 2) + n` are all work,
                                however the threads are scheduled
                                afterwards
* `INet.Arith.two_threads_slower`, `INet.Arith.two_threads_factor`
                                which passes the whole work of one thread
                                for `m` from five on, and `c` times that
                                work for `m` from thirteen times `c` on
* `INet.XMach.reader`, `INet.XMach.trace_sweep`, `INet.XMach.trace_readers`,
  `INet.XMach.work_readers`     any number of threads acting in turn while
                                all but the first leave the memory as it
                                is: the memory and the claims are those of
                                the first thread alone, and the work is
                                its work and the actions of the others
* `INet.XMach.act_wires_sub`, `INet.XMach.act_gone`
                                an action removes no segment, and an agent
                                that is gone stays gone
* `INet.XMach.solo_direct_keeps`, `INet.XMach.solo_via_keeps`
                                a round takes only its pair: any other
                                agent is in memory after each of its
                                actions
* `INet.XMach.work_energy`, `INet.XMach.work_tail`,
  `INet.XMach.work_after_reading`
                                the measure of the general bound in the
                                open: from any moment of any run, the work
                                to come is at most the shares of the
                                threads and a pass for each claim to come
* `INet.Arith.TailOk`, `INet.Arith.ReadList`, `INet.Arith.readList_turn`,
  `INet.Arith.Reads`, `INet.Arith.Reads.step`, `INet.Arith.rr_reads`
                                on an addition a thread whose list is the
                                list of agents turned by its number only
                                reads while the first thread makes all its
                                claims but two: what it can be at each
                                moment, with the actions it has left and
                                the number it has made, exact up to one;
                                and to the end when it does not come to
                                the zero of the first argument while the
                                last pair is ready
* `INet.Arith.solo_hist`, `INet.Arith.solo_link`, `INet.Arith.solo_no_link`
                                the segment from an adder to the next is
                                in memory from the end of the round that
                                makes the next, and not before that round
                                starts; so the walk of a thread from the
                                top of the second argument has as many
                                hops as there are rounds written
* `INet.Arith.threads_any_second`
                                so `k + 1` threads acting in turn add
                                `m + 1` and `n` in at most
                                `116 * m + 33 * n + 267` actions that are
                                not rests and `48 * m + 15 * n + 85` for
                                each of the `k` others, for `k + 3 ≤ m`,
                                `20 * k ≤ 3 * m + 3 * n + 22` and every
                                `n`, however they are scheduled after the
                                first `(k + 1) * (17 * m - 1)` actions
* `INet.Arith.threads_round_robin`, `INet.Arith.threads_rest`,
  `INet.Arith.turn_quiet`       and when `48 * n ≤ 221 * m + 61` or
                                `221 * m + 51 * k + 217 ≤ 48 * n`, which
                                leaves out about `k + 3` values of `n` for
                                each `m`, in the work
                                of one thread and at most
                                `4 * m + 3 * n + 15` more for each of the
                                others, and no less; they are at rest when
                                each has had the actions that one thread
                                needs
* `INet.Arith.solo_fin`, `INet.Arith.solo_alive_zero`,
  `INet.Arith.solo_gone_zero`   one thread to the end of its run: every
                                segment it has is one of the memory it
                                leaves, the second argument and the zero
                                of the first are in memory until its
                                action `17 * m + 22` takes that zero, and
                                the zero is gone from then on
* `INet.Arith.two_threads_round_robin`, `INet.Arith.two_threads_any_second`,
  `INet.Arith.three_threads_round_robin`,
  `INet.Arith.three_threads_any_second`
                                the cases of two threads, `m` from four
                                on, and of three, `m` from six on
* `INet.Arith.two_threads_long`, `INet.Arith.two_threads_narrow`
                                two threads: at most `26 * m + 6 * n + 50`
                                unless `48 * n` lies strictly between
                                `221 * m + 61` and `221 * m + 268`, five
                                values of `n` at most
* `INet.Arith.solo_no_link3`, `INet.Arith.solo_adder_alive`,
  `INet.Arith.solo_gone_adder`, `INet.Arith.solo_final_mem`,
  `INet.Arith.Final.pass_stays` one thread inside its last rounds: the
                                segment from the lowest successor to the
                                last adder is written at the action
                                `17 * m + 10`, the last adder is in memory
                                from `17 * m + 7` to `17 * m + 20` and
                                gone from `17 * m + 21` on, and from
                                `17 * m + 25` on the memory stays as it
                                is: the last pass only reads
* `INet.Arith.two_threads_entry`
                                two threads in turn, any second argument:
                                the second only reads and the tight bound
                                holds, or there is a moment, when each has
                                made between `17 * m + 11` and
                                `17 * m + 20` actions, at which the memory
                                and the first thread are those of one
                                thread alone and the second is ready to
                                take the zero of the first argument, with
                                the zero of the second argument and the
                                top successor left in its list
* `INet.Sweeps`, `INet.XMach.work_pair_after`, `INet.XMach.work_two_stays`
                                two threads in turn, a pair of actions at
                                a time: the work after any number of
                                pairs, and the work of two threads that
                                only read in a memory that stays as it is
* `INet.XMach.work_full`, `INet.XMach.Total`, `INet.XMach.total_two_stays`,
  `INet.XMach.Total.after`, `INet.XMach.Ends`, `INet.XMach.ends_sweeps`
                                work to the action: while no thread is at
                                rest every action is work, two threads
                                that only read do exactly the work of
                                each, and so a run followed to its end
                                comes to a work that is known exactly
* `INet.Arith.RaceBase`, `INet.Arith.race_write`,
  `INet.Arith.RaceBase.states`, `INet.Arith.race_reader_wins`,
  `INet.Arith.race_d0` to `INet.Arith.race_d9`
                                the race for the last pair, one case for
                                each of the ten moments, with the exact
                                work from there on: in nine the
                                second thread takes the zero and the
                                adder, writes the two segments and starts
                                over, while the first writes the end of
                                its round or reads on to the zero and
                                finds it gone; in one the first thread
                                takes the adder first, the second puts the
                                zero back and the first takes it
* `INet.Arith.raceWork`, `INet.Arith.two_threads_exact`
                                so with two threads in turn, `m` from four
                                on and every `n`, either the second only
                                reads, or it is ready to take the zero
                                after `17 * m + 11 + d` actions of each,
                                `d` up to nine, and the work of the whole
                                run is exactly `44 * m + 6 * n + c`, with
                                `c` one of 52, 53, 54, 56, 61, 62, 63, 64
                                and 68 as `d` goes up, or
                                `39 * m + 3 * n + 60` for `d = 8`, where
                                the first thread keeps the pair
* `INet.Arith.two_threads_race` in every case at most
                                `44 * m + 6 * n + 68` actions that are not
                                rests
* `INet.Arith.solo_link_top9`, `INet.Arith.solo_link8`,
  `INet.Arith.solo_no_link8`, `INet.Arith.solo_link3`,
  `INet.Arith.solo_snd_forever`
                                one thread to the action: the segment
                                from an adder to the next is the first
                                that its round writes, in memory when the
                                thread has made `17 * d + 8` actions, `d`
                                the number of the round, and not before;
                                the second argument stays in memory to the
                                end
* `INet.Arith.RdAt`, `INet.Arith.RdAt.chain`, `INet.Arith.RdAt.walk`,
  `INet.Arith.RdAt.snd`, `INet.Arith.twoAt`,
  `INet.Arith.two_reader_at_zero`
                                the second of two threads, action by
                                action: three for each successor of its
                                chain, a walk of `(3 * m + 11) / 16` hops
                                from the top of the second argument, three
                                for each agent below it, one for the first
                                adder; it comes to the zero of the first
                                argument after exactly `twoAt m n` actions
* `INet.Arith.two_entry_exact`, `INet.Arith.two_threads_race_at`
                                the race takes place exactly when
                                `twoAt m n` is `17 * m + 7 + d` with `d`
                                up to nine, and the work is then
                                `raceWork m n d`
* `INet.Arith.quiet_total`, `INet.Arith.two_threads_early`,
  `INet.Arith.two_threads_late`, `INet.Arith.two_threads_after`,
  `INet.Arith.two_threads_zero`
                                outside the race the second thread only
                                reads, and the work is that of one thread
                                and the actions of the second before it
                                rests: `twoAt m n` and seven, eight or
                                five more as it passes the zero of the
                                first argument early, finds the last adder
                                gone, or finds that zero gone
* `INet.Arith.twoWork`, `INet.Arith.two_threads_total`
                                so two threads in turn add `m + 1` and `n`
                                in exactly `twoWork m n` actions that are
                                not rests, for `m` from four on and every
                                `n`: 1,496 on `21 + 94`, 285 on `5 + 23`
                                and 1,105 on `21 + 93` are theorems
* `INet.Arith.RdAt.chain_turn`, `INet.Arith.RdAt.tops`,
  `INet.Arith.turnAt`, `INet.Arith.turnRest`,
  `INet.Arith.turn_reader_quiet`, `INet.Arith.turn_reader_zero`
                                the thread numbered `t + 1` of any number,
                                action by action: it comes to the zero of
                                the first argument after exactly
                                `turnAt m n t` actions and, outside the
                                ten moments of the race, rests after
                                exactly `turnRest m n t`; its `t + 1` top
                                successors cost one action each
* `INet.Arith.Quiet`, `INet.Arith.quiet_total_all`,
  `INet.Arith.threads_total`    so `k + 1` threads in turn add `m + 1` and
                                `n` in exactly the work of one thread and
                                `turnRest m n t` for each other thread,
                                for `k + 1 ≤ m`,
                                `20 * k ≤ 3 * m + 3 * n + 21` and every
                                size where no thread comes to that zero
                                after `17 * m + 7` to `17 * m + 16`
                                actions: 300 for three threads on `7 + 9`
* `INet.Arith.third_quiet`, `INet.Arith.third_total`,
  `INet.Arith.three_entry`      a third thread that only reads does not
                                disturb two threads in turn: the run of
                                the three is the run of the two with that
                                thread beside it, and the work is theirs
                                and its busy actions
* `INet.Arith.three_threads_race_first`
                                three threads in turn, the second in the
                                race and the third past the zero of the
                                first argument: the work is exactly
                                `raceWork m n d` and `turnRest m n 1`
                                (612 on `7 + 30`)
* `INet.Arith.Sweeps3`, `INet.Arith.total_three_stays`,
  `INet.Arith.total3_sweeps`    three threads in turn, three actions at a
                                time, followed to the end of the run:
                                three threads that only read do exactly
                                the work of each
* `INet.Arith.race_wins3_a`, `INet.Arith.race_wins3_b`,
  `INet.Arith.race3_d6_a` to `INet.Arith.race3_d9_b`
                                the race for the last pair with a thread
                                reading between the two: eight cases, the
                                four moments at which the first thread is
                                past its last round, each with the second
                                thread about to pop the zero of the first
                                argument or one action past it
* `INet.Arith.three_threads_race_third`
                                three threads in turn, the third in the
                                race and the second coming to that zero
                                after the ten moments: the work is exactly
                                `raceWork m n d`, `turnAt m n 0 + 8` for
                                the second thread, and one more when the
                                first thread keeps the pair (653 on
                                `7 + 33`, 594 on `8 + 38`)
* `INet.Arith.race3_d0_a` to `INet.Arith.race3_d5_b`
                                the same race at its first six moments,
                                where the first thread is still writing
                                its round on the lowest successor, starts
                                over, or is about to pop the last adder:
                                twelve cases
* `INet.Arith.three_threads_race_both`,
  `INet.Arith.three_threads_race_late`
                                three threads in turn with the third in
                                the race, wherever the second is: the
                                work is exactly `raceWork m n d` and
                                `turnAt m n 0 + 8`, one more for `d = 8`
* `INet.Arith.threeWork`, `INet.Arith.three_threads_total`
                                so three threads in turn add `m + 1` and
                                `n` in exactly `threeWork m n` actions
                                that are not rests, for `m` from four on
                                and `19 ≤ 3 * m + 3 * n`: 624 on
                                `7 + 31`, 641 on `7 + 32` and 718 on
                                `8 + 36` are theorems
* `INet.Arith.Row`, `INet.Arith.sweep_two`, `INet.Arith.SweepsK`,
  `INet.Arith.total_stays`, `INet.Arith.entry_all`
                                any number of threads in turn: a turn of
                                each with two of them writing and the
                                others reading, between the two or after
                                them; any number of threads that only
                                read do exactly the work of each; and the
                                run while all but the first only read
* `INet.Arith.RaceViews`, `INet.Arith.Beside`, `INet.Arith.beside_adj_a`,
  `INet.Arith.beside_adj_b`, `INet.Arith.beside_late_s`,
  `INet.Arith.beside_late_l`    the five memories that the threads between
                                the two of a race read in, and what a
                                thread does beside the race: the thread
                                next to the one that takes the pair reads
                                on to the last adder and finds it gone, a
                                thread two or three actions from the zero
                                of the first argument finds that zero gone
* `INet.Arith.race_wins_k`, `INet.Arith.race_k_d0` to
  `INet.Arith.race_k_d9`        the ten cases of the race with any number
                                of threads reading between the two, each
                                to the end of the run
* `INet.Arith.four_threads_race_last`
                                four threads in turn with the fourth in
                                the race: the work is exactly
                                `raceWork m n d`, two more for `d = 8`,
                                `turnAt m n 1 + 9` for the third thread
                                and `turnAt m n 0 + 5` for the second
                                (752 on `7 + 32`, 744 on `8 + 39`)
* `INet.Arith.trace_prefix`, `INet.Arith.beside_end`,
  `INet.Arith.total_beside_end` one more thread at the end that only reads
                                and comes to rest adds exactly its actions
                                to the work of the others, whatever they
                                do
* `INet.Arith.trace_gone`, `INet.Arith.act_reads`, `INet.Arith.RdAt.three`
                                an agent that is gone and that no thread
                                holds stays gone under any schedule; a
                                thread that is idle or looking for a
                                partner only reads, and the three actions
                                after it is idle read
* `INet.Arith.threads_early_last`, `INet.Arith.threads_early_many`
                                a thread that passes the zero of the first
                                argument before the race only reads,
                                whatever the threads before it do, and
                                adds exactly `turnRest m n t` to their
                                work; so do any number of such threads
* `INet.Arith.fourWork`, `INet.Arith.four_threads_total`
                                so four threads in turn add `m + 1` and
                                `n` in exactly `fourWork m n` actions that
                                are not rests, for `m` from four on and
                                `39 ≤ 3 * m + 3 * n`: 725 on `7 + 30`,
                                740 on `7 + 31` and 752 on `7 + 32` are
                                theorems
* `INet.Arith.threads_beyond_four`
                                and five threads or more when the fifth
                                passes that zero before the race: 984 for
                                five threads on `8 + 36`, 1,956 for six on
                                `14 + 64`
* `INet.Arith.LateMem`, `INet.Arith.LP`, `INet.Arith.beside_late`,
  `INet.Arith.turn_reader_lp`   a thread that is still on the second
                                argument when the race starts reads on in
                                each of the five memories of the race and
                                finds the zero of the first argument gone
* `INet.Arith.entry_range`, `INet.Arith.beside_range`
                                the threads between the two that race,
                                given by their number
* `INet.Arith.threads_race_last`
                                so any number of threads in turn, the last
                                of them in the race, are exact
* `INet.Arith.racerOf`, `INet.Arith.allWork`, `INet.Arith.threads_exact`
                                any number of threads in turn, every size,
                                to the action: `k + 1` threads add `m + 1`
                                and `n` in exactly `allWork m n k` actions
                                that are not rests, for `m` from four on,
                                `k + 1 ≤ m` and
                                `20 * k ≤ 3 * m + 3 * n + 21`: 1,014 for
                                five threads on `8 + 38`, 1,284 for seven
                                on `8 + 38`, 2,258 for eight on `13 + 60`
* `INet.Arith.allWork_succ_out`, `INet.Arith.allWork_succ`
                                what one more thread adds to that work:
                                exactly `turnRest m n k` when it is not in
                                the race, and in every case at least the
                                `turnAt m n k` actions that bring it to
                                the zero of the first argument and at most
                                two fewer than the work of one thread
* `INet.Arith.threads_more`, `INet.Arith.threads_bounds`
                                so one more thread in turn never saves
                                work, and `k + 1` threads do at least the
                                work of one and `3 * n + 4` for each other
                                thread, at most `k + 1` times the work of
                                one less two for each other thread (two
                                threads on `6 + 28` make 456, one 229)
* `INet.Arith.Rounds`, `INet.Arith.rounds_readers`
                                the rounds a run of threads in turn takes
                                before all are at rest; when every thread
                                but the first only reads, they are the
                                actions of the first alone
* `INet.Arith.threads_rounds`, `INet.Arith.threads_overhead`
                                so outside the race `k + 1` threads in
                                turn take exactly `soloWork (m + 1) n`
                                rounds, as one thread does, and make its
                                work and `turnSum m n k` more: 273 rounds
                                for three threads on `8 + 28`, 313 for
                                five on `9 + 34`
* `INet.Arith.threads_rounds_ge`, `INet.Arith.two_threads_rounds_ge`
                                in every case the rounds are at least the
                                work shared among the threads; so two
                                threads in the race end at most nine
                                rounds sooner than one, unless the first
                                thread keeps the pair
* `INet.Arith.RaceEnd`, `INet.Arith.race_e_d0` to `INet.Arith.race_e_d9`
                                each case of the race gives the five
                                actions of the race and what the first
                                thread and the last still do after it
* `INet.Arith.rounds_stays`, `INet.Arith.rounds_sweepsK`
                                the rounds of a run that ends with every
                                thread reading are those of the thread
                                that reads longest
* `INet.Arith.raceSave`, `INet.Arith.two_threads_race_rounds`,
  `INet.Arith.two_threads_rounds`, `INet.Arith.two_threads_rounds_bounds`
                                so two threads in turn take exactly
                                `twoRounds m n` rounds, for `m` from four
                                on: those of one thread outside the race,
                                and 9, 8, 7, 6, 4, 4, 3, 2, 0 or 0 fewer
                                in it (211 rounds on `6 + 25`, where one
                                thread takes 220)
* `INet.Arith.early_reader_end`, `INet.Arith.threads_early_many_rounds`
                                a thread that passes the zero of the first
                                argument before the race is at rest long
                                before the run ends, so any number of them
                                leave the rounds as they are
* `INet.Arith.BesideBy`, `INet.Arith.RaceEnd.rounds`,
  `INet.Arith.threads_race_last_rounds`
                                the threads between the two that race are
                                at rest before them, so with any number of
                                threads, the last in the race, the rounds
                                are those of the race of two
* `INet.Arith.allRounds`, `INet.Arith.threads_rounds_exact`,
  `INet.Arith.threads_rounds_bounds`
                                any number of threads in turn, every size,
                                the rounds to the action: `k + 1` threads
                                are at rest after exactly `allRounds m n k`
                                rounds, never more than one thread alone
                                and at most nine fewer (290 rounds for
                                three threads on `8 + 36`, 405 for six on
                                `11 + 52`, where one thread takes 297 and
                                411)
* `INet.Arith.tagNet`, `INet.Arith.beside`, `INet.Arith.twoSums`
                                two additions side by side in one net, the
                                names of each tagged at the end, where a
                                tag is kept by every interaction
* `INet.Arith.twoSolo`, `INet.Arith.two_sums_one_thread`,
  `INet.Arith.two_sums_two_threads`
                                on that net, for the sizes computed, one
                                thread takes the rounds of each addition
                                and one more pass over what the first has
                                left, and two threads in turn take fewer
                                rounds, by two at least
* `INet.Arith.two_sums_2_2`, `INet.Arith.two_sums_4_3`
                                `2 + 2` twice: 147 rounds for one thread,
                                106 for two, 86 for three, with 147, 191
                                and 255 actions of work; `4 + 3` twice:
                                254 rounds and 174
* `INet.Arith.Looks`, `INet.Arith.Looks.fired`, `INet.Arith.Looks.round_first`,
  `INet.Arith.Looks.round_later`, `INet.Arith.Looks.round_zero`
                                a net seen inside a larger memory: the
                                cells with its tag are the net, a thread
                                finds there what it finds in the net
                                alone, and a pair fires as in the net
                                alone, in as many actions
* `INet.Arith.Looks.pass`, `INet.Arith.pass_two`
                                a thread that only reads passes the cells
                                of a net inside a larger memory as it
                                does on the net alone; so the last pass
                                over two nets takes the actions of each
* `INet.Arith.Looks.rounds_all`, `INet.Arith.two_sums_solo_works`,
  `INet.Arith.two_sums_solo`    so one thread on two additions side by
                                side takes exactly `twoSolo` rounds, for
                                every size with `m` and `m'` from one on:
                                415 on `6 + 10` twice, 1,135 on `20 + 30`
                                beside `12 + 40`
* `INet.Arith.rule_tag`, `INet.Arith.Looks.act`, `INet.Arith.Inside.act`,
  `INet.Arith.Inside.solo`      every action of a thread on a net inside a
                                larger memory, taking, writing and the
                                reload included, is its action on the net
                                alone, and leaves the cells with another
                                tag untouched; so its run is the run on
                                the net alone
* `INet.Arith.Inside.reader`, `INet.Arith.beside_stretch`
                                two nets side by side, two threads: while
                                the second thread reads its way through
                                the first net, the run is the run on that
                                net alone
* `INet.Arith.reader_top`, `INet.Arith.two_sums_stretch`
                                two additions: after `turnRest m n 0 - 1`
                                rounds the second thread has passed the
                                first addition and stands before the
                                second, which is untouched
* `INet.Arith.Looks.claim_acts`, `INet.Arith.claim_rounds`,
  `INet.Arith.two_sums_second_claim`, `INet.Arith.two_sums_second_reload`
                                it claims the first pair of the second
                                addition in round `turnRest m n 0 + 3` and
                                has the whole memory as its list after
                                round `turnRest m n 0 + 14`
* `INet.Arith.two_sums_first_done`, `INet.Arith.two_sums_one_claim`,
  `INet.Arith.head_start`       one thread claims that pair with its
                                action `22 * m + 3 * n + 39`: with two
                                threads the second addition starts at
                                least `18 * m + 20` rounds sooner
* `INet.Arith.crossLaw`, `INet.Arith.first_collision_checked`
                                where the two threads first collide, by
                                the round modulo seventeen in which the
                                second comes to the second addition:
                                checked by the kernel on `6 + n` beside
                                `2 + 0` for the seventeen phases
* `INet.Arith.rule_cost`, `INet.Arith.act_cost`, `INet.Arith.trace_cost`,
  `INet.Arith.rest_cost`        the price of an interaction, whatever the
                                threads and the schedule: sixteen actions
                                of the thread that claims it, less eight
                                if it ends an adder; a run that ends at
                                rest has done sixteen actions of work for
                                each claim, less eight for each adder of
                                the net
* `INet.Arith.Parts.matching`, `INet.Arith.beside_wf`,
  `INet.Arith.rest_claims_eq`   two well-formed nets side by side are a
                                well-formed net, and runs on it that end
                                at rest make the same number of claims
* `INet.Arith.two_sums_claims`, `INet.Arith.two_sums_work_ge`,
  `INet.Arith.two_sums_rounds_ge`, `INet.Arith.two_threads_two_sums_ge`
                                what threads can save on two additions:
                                a run that ends at rest has made
                                `m + m' + 4` claims and done at least
                                `16 * (m + m' + 3)` actions of work, so
                                `c` threads in turn take at least that
                                many rounds divided by `c`, two threads
                                at least `8 * (m + m' + 3)`
* `INet.Arith.sum_claims`, `INet.Arith.sum_work_ge`,
  `INet.Arith.sum_rounds_ge`    and on one addition: `m + 2` claims, at
                                least `16 * m + 24` actions of work
* `INet.Arith.stays_act`, `INet.Arith.claim_rounds_read`,
  `INet.Arith.write_rounds_read`, `INet.Arith.zero_rounds_read`
                                rounds of two threads on two nets side by
                                side in which one thread only reads on
                                its net while the other claims a pair,
                                writes and reloads
* `INet.Arith.reader_ones`, `INet.Arith.ones_first_reads`,
  `INet.Arith.ones_two_threads`, `INet.Arith.ones_saving`
                                a saving proved for every size of a
                                family: on `1 + n` beside `1 + n'` with
                                `n` at least seven, two threads take
                                exactly `6 * n + 3 * n' + 50` rounds,
                                thirty fewer than one thread
* `INet.Arith.first_reads`, `INet.Arith.later_rounds_read`,
  `INet.Arith.later_many_read`, `INet.Arith.reader_two`,
  `INet.Arith.apart_second`, `INet.Arith.apart_two_threads`,
  `INet.Arith.apart_saving`, `INet.Arith.apart_family`,
  `INet.Arith.twice_family`
                                the same for every first argument: on
                                `(m + 1) + n` beside `(m' + 1) + n'` with
                                `m'` at most `m` and `n` at least
                                `5 * m + 7`, two threads take exactly
                                `8 * m + 6 * n + 22 * m' + 3 * n' + 50 +
                                (3 * m + 11) / 16` rounds, at least
                                `18 * m + 29` fewer than one thread
* `INet.Arith.act_succs`, `INet.Arith.act_cost2`, `INet.Arith.trace_read`,
  `INet.Arith.rest_read`, `INet.Arith.two_sums_rounds_read`,
  `INet.Arith.two_sums_rounds_floor`, `INet.Arith.two_threads_read_ge`
                                a limit that counts the reading: any
                                number of threads under any schedule,
                                at rest, have done fifteen actions for
                                each interaction and, each thread, as
                                many as the net has successors less the
                                number of threads; so `c` threads in
                                turn on two additions take more than
                                `m + n + m' + n' + 2 - c` rounds
* `INet.Arith.rule_color`, `INet.Arith.act_inv`, `INet.Arith.trace_ok`,
  `INet.Arith.two_sums_memOk`, `INet.Arith.two_sums_snd_forever`,
  `INet.Arith.act_cost3`, `INet.Arith.rest_read3`,
  `INet.Arith.two_sums_rounds_read3`, `INet.Arith.two_sums_rounds_floor3`,
  `INet.Arith.two_threads_read3_ge`
                                the successors of the second arguments
                                are never taken, under any schedule; so
                                each thread spends three actions on each,
                                and `c` threads in turn on two additions
                                take more than
                                `m + m' + 3 * (n + n') + 2 - c` rounds
* `INet.Arith.act_lam`, `INet.Arith.rr_step`, `INet.Arith.trace_first`,
  `INet.Arith.act_phase1`, `INet.Arith.phase1`, `INet.Arith.late_floor`,
  `INet.Arith.two_sums_untouched`, `INet.Arith.two_sums_rounds_late`
                                with `m + 2` threads or fewer in turn,
                                nothing of the second addition is touched
                                in the first `3 * n` rounds; some thread
                                claims after them and reads the memory
                                again, so the rounds and the threads are
                                together at least
                                `6 * n + 3 * n' + m + m' + 4`
* `INet.Arith.seg_cost`, `INet.Arith.trace_bnd`, `INet.Arith.claim_rest`,
  `INet.Arith.late_floor2`, `INet.Arith.two_sums_rounds_late2`,
  `INet.Arith.two_threads_late2`
                                and the interactions of the second
                                addition come after those rounds, sixteen
                                actions each among the threads: two
                                threads in turn take at least
                                `6 * n + 3 * n' + m + 9 * m' - 6` rounds
* `INet.Arith.two_sums_rounds_late3`, `INet.Arith.two_sums_untouched2`,
  `INet.Arith.phase1s`, `INet.Arith.two_sums_untouched_any`
                                the same limit for up to `m + n + 2`
                                threads, with three rounds less for each
                                thread beyond `m + 2`; and under any
                                schedule nothing of the second addition
                                is touched before some thread has made
                                `3 * n` actions of its own
* `INet.Arith.two_sums_rest_census`, `INet.Arith.two_sums_apart`,
  `INet.Arith.two_sums_succs_each`, `INet.Arith.trace_tag`,
  `INet.Arith.trace_census`, `INet.Arith.trace_zf`
                                what the memory holds at rest, with any
                                number of threads and any schedule: no
                                adder, the `m + n` and `m' + n'`
                                successors of the two results, each in
                                its own net, one zero in each net, and
                                nothing else; and no segment ever joins
                                the two nets
* `INet.Arith.two_sums_rest_num`, `INet.Arith.two_sums_fair`,
  `INet.Arith.sum_rest_num`, `INet.Arith.rest_mem_eq`,
  `INet.Arith.Within.isNum`
                                and the two results are there: with any
                                number of threads and any schedule, a
                                memory at rest has the numeral `m + n`
                                on the free port of the first net and
                                `m' + n'` on that of the second; under a
                                fair schedule the run comes to rest
* `INet.Arith.two_sums_rest`, `INet.Arith.two_sums_fair_all`,
  `INet.Arith.two_sums_census`, `INet.Arith.two_sums_normal`,
  `INet.Arith.beside_normal`, `INet.Arith.Inside.works`
                                the same for all arguments, a first
                                argument of zero included: the claims,
                                the two numerals and the count of the
                                agents at rest; two nets side by side
                                reduce as each does alone
* `INet.Arith.two_sums_exact`, `INet.Arith.numerals_cover`,
  `INet.Arith.NumList`, `INet.Arith.NumList.nodup`,
  `INet.Arith.nodup_cover`
                                and nothing else is there: at rest
                                every agent in memory is one of the
                                `m + n + 1` agents of the first numeral
                                or one of the `m' + n' + 1` of the
                                second, each numeral in its own net
* `INet.Arith.sums_rest`, `INet.Arith.sums_fair`,
  `INet.Arith.sums_normal`, `INet.Arith.besides_normal`,
  `INet.Arith.besides_wf`, `INet.Arith.phases`
                                any number of additions side by side:
                                with any number of threads and any
                                schedule, a run that ends at rest has
                                made `m + 1` claims for each addition
                                and has every sum on its free port; any
                                number of nets side by side reduce as
                                each does alone
* `INet.Arith.sums_census`, `INet.Arith.sums_exact`,
  `INet.Arith.numerals_all`, `INet.Arith.sums_memOk`
                                and for any number of additions too the
                                memory at rest holds no adder, the
                                successors of every sum and one zero
                                for each, and every agent in it is an
                                agent of the numeral of one of the sums
* `INet.Arith.besides_rest`, `INet.Arith.besides_fair`,
  `INet.Arith.besides_reduce`, `INet.Arith.besides_rest_num`,
  `INet.XMach.made_rest`, `INet.XMach.made_fair`,
  `INet.Net.Made.reduce`, `INet.Net.Made.step`, `INet.Net.Made.normal`
                                any nets with normal forms side by
                                side, in any system whose rules give
                                every new agent a side: with any number
                                of threads and any schedule, a run that
                                ends at rest has made as many claims as
                                the reductions of the nets have steps,
                                and the memory is made of their normal
                                forms, each under its tag
* `INet.Step.plug`, `INet.Steps.plug`, `INet.Net.WF.plug`,
  `INet.Net.Conn.plug`
                                free ports wired together: a reduction
                                of a net is a reduction of the net with
                                any of its free ports joined by new
                                segments, in any system; the net stays
                                well formed, and two wires that ended
                                at joined ports are one wire
* `INet.Arith.sum3_rest`, `INet.Arith.sum3_fair`,
  `INet.Arith.sum3_normal`, `INet.Arith.add_add`
                                one addition after another: the net for
                                `(m + n) + k`, the result of the first
                                adder wired to the second, with any
                                number of threads and any schedule: a
                                run that ends at rest has made `m + 1`
                                and `m + n + 1` claims and has the
                                numeral `m + n + k` on its free port
* `INet.Arith.Expr.rest`, `INet.Arith.Expr.fair`,
  `INet.Arith.Expr.good`, `INet.Arith.add_evals`, `INet.Net.Made.wf`
                                every expression built from numerals
                                and additions has a net; with any
                                number of threads and any schedule a
                                run on it that ends at rest has made,
                                for each addition, one more claim than
                                the value of its first argument, and
                                has the numeral of the value of the
                                expression on its free port
* `INet.Arith.Expr.assoc_rest`, `INet.Arith.Expr.cost_assoc`,
  `INet.Arith.Expr.cost_comm`
                                the two ways of bracketing three terms
                                give the same numeral, and the left one
                                makes exactly the value of the first
                                term more claims, under any schedules
* `INet.Arith.Expr.run_sound`, `INet.Arith.Expr.run_complete`,
  `INet.XNet.runRead_sound`, `INet.XNet.runRead_complete`,
  `INet.XNet.readNum_sound`, `INet.XNet.readNum_complete`,
  `INet.Addition.IsNum.unique`
                                an expression can be run: threads take
                                turns on its net for a number of
                                actions and the result is read off the
                                memory; whatever is returned is the
                                value of the expression, and with
                                enough actions the value is returned
* `INet.Steps.context`, `INet.XMach.union_rest`, `INet.XMach.union_fair`,
  `INet.Net.Apart.reduce`, `INet.Net.WF.union`, `INet.Net.Apart.normal`
                                in any system, a net reduces inside a
                                larger net as it does alone, when the
                                names of the two are apart; two nets
                                with normal forms side by side come out
                                right with any number of threads and
                                any schedule
* `INet.XMach.part_first`, `INet.Steps.part_first`,
  `INet.XMach.unions_rest`, `INet.Net.unions_reduce`
                                in any system, a part of a net can be
                                reduced first: the claims of a run are
                                those of the part and of what is left;
                                and any number of nets with names apart
                                come out right side by side
* `INet.XNet.normalize_steps`   what the list reducer returns after `k`
                                steps is the compact form of a normal
                                form reached in `k` steps of reduction
* `INet.XMach.tagged_rest`      two nets side by side under tags, in any
                                system: at rest the memory holds the
                                two normal forms up to the names of the
                                agents made on the way
* `INet.Arith.round_robin_beats_turns`
                                two threads acting in turn do less work
                                than the same threads claiming in turn
* `INet.Arith.solo_alive`       on an addition, through the first rounds
                                of one thread, every agent of the start
                                that those rounds do not take is in memory
                                after every action, so a thread that reads
                                makes three actions on each successor of
                                its chain and on each agent of the second
                                argument

Closed loops.  `Net.Dead` marks the components of the wiring that reach no
end, `Net.DeadCount` counts them, and `Loops` counts the loops closed by a
reduction: the dead components gained, minus one per step.

* `INet.Site.dead_fire`, `INet.Site.dead_fire_principal`,
  `INet.Site.dead_fire_cases`  dead components are permanent; a firing kills
                                the wire between the two principal ports and
                                nothing else but loops through the auxiliary
                                ports of the pair
* `INet.Site.deadCount_fire`    a net with `n` dead components has
                                `n + 1 + ℓ` after a firing, and `ℓ = 0`
                                exactly when no auxiliary port has died
* `INet.Site.dead_of_loop`      a wire that a rule closes onto itself dies,
                                also when it is a single segment that the
                                firing merely doubles
* `INet.Net.DeadCount.unique`, `INet.Steps.loops`, `INet.loops_unique`
                                the count is well defined, every reduction
                                closes a definite number of loops, and all
                                reductions to normal form close the same
                                number
* `INet.Site.auxCount_of_compact`, `INet.Site.auxCount_of_nbhd`
                                the loops closed by a firing are the same
                                with and without history, and in a net
                                without history they are those closed in the
                                neighbourhood of the pair
* `INet.XNet.runLoops_loops`, `INet.XNet.runLoops_unique`,
  `INet.XNet.runLoops_isSome`  the list reducer counts the loops: on a valid
                                input it always returns a count, the count is
                                the number of loops of a reduction that it
                                follows, and when it stops on a normal form
                                it is the number of loops of every reduction
                                to normal form
* `INet.HNet.runLoops_loops`, `INet.HNet.runLoops_unique`,
  `INet.HNet.runLoops_isSome`  the same for the hash-map reducer, which
                                counts in the neighbourhood of each pair
* `INet.Comb.xloop_normalize`, `INet.Comb.xloop_loops`,
  `INet.Comb.xloop_runLoops`   an annihilation after which the reducer
                                returns the empty net, which closes exactly
                                two loops, and for which the reducer reports
                                two

An executable reducer.  `XNet` is a finite net without history, as data;
`XNet.step` finds an active pair and fires it, rewiring as it goes;
`XNet.run` iterates it.

* `INet.XNet.step_sound`     a step of the reducer is a `CStep` and
                             preserves the invariant `XNet.Ok`
* `INet.XNet.step_complete`  the reducer stops only on normal forms
* `INet.XNet.run_normal`     if the reducer stops, it has returned the normal
                             form; the number of steps it took is the length
                             of every reduction to normal form, and no
                             reduction is longer
* `INet.XNet.run_complete`   conversely, if the input has a normal form
                             reached in `k` steps and the fuel is at least
                             `k`, the reducer stops after exactly `k` steps
                             on that normal form
* `INet.XNet.parStep_spec`, `INet.XNet.parStep_fires_all`
                             a second reducer, `XNet.parStep`, fires every
                             active pair of the net in one round; a round is
                             a reduction with one step per pair
* `INet.XNet.parRun_eq_run`, `INet.XNet.parRun_complete`
                             when both reducers stop they return the same
                             net after firing the same number of pairs, and
                             the parallel one stops whenever a normal form
                             exists and it is given enough rounds
* `INet.XNet.run_map`        the reducer does not depend on names: on a
                             renamed input it stops after the same number of
                             steps, on a renaming of its output
                             (`INet.Comb.xgd_map_run` is an instance)
* `INet.XNet.check_iff_ok`   the executable check `XNet.check` passes exactly
                             on the nets satisfying `XNet.Ok`, which is
                             therefore decidable
* `INet.XNet.normalize_spec`, `INet.XNet.normalize_complete`
                             `XNet.normalize` validates its input, runs the
                             reducer and returns a result only if it has
                             stopped; whatever it returns is the normal
                             form, and it does return it when the input is
                             valid, has a normal form and the fuel suffices
* `INet.Comb.xsystem`, `INet.Comb.xgg_run`, `INet.Comb.xgg_normal_form`
                             the combinators as an executable system, a run
                             evaluated by the kernel, and its result
                             identified as a normal form
* `INet.Comb.xgd_normalize`, `INet.Comb.xgd_normal_form`,
  `INet.Solo.xaa_normalize`  a commutation and the single-agent rule, each
                             validated and normalized by evaluation alone
* `INet.SysData.toXSys`      an executable system built from tables of rules;
                             the only proof it takes is the evaluation of
                             `SysData.check`
* `INet.SysData.check_iff`   that check accepts exactly the tables in which
                             every right-hand side has no shadowed entry,
                             is well formed, and has its mirror image
                             listed for the reversed pair
* `INet.Comb.dsystem`        the combinators defined that way; they reduce
                             the example nets exactly as `Comb.xsystem` does
* `INet.XNet.ok_iff_matching`, `INet.Net.Matching.insert1`
                             the valid inputs of the reducer are the nets
                             whose segments are a perfect matching of their
                             ends; inserting an agent on a segment of one
                             gives another
* `INet.HNet.fire_toNet`, `INet.HNet.step_sound`, `INet.HNet.step_complete`,
  `INet.HNet.run_normal`, `INet.HNet.run_complete`
                             a third reducer, `HNet`, on hash maps with a
                             work list of active pairs: a step fires the
                             neighbourhood of a pair and writes it back; it
                             is a `CStep`, stops only on normal forms,
                             returns the normal form and finds it whenever
                             the fuel suffices
* `INet.HNet.run_eq_run`, `INet.HNet.run_of_run`
                             it agrees with the list reducer, and stops
                             whenever the list reducer does
* `INet.HNet.runC_val`, `INet.HNet.fireC_bound`, `INet.HNet.runC_cost`
                             its cost: the same reducer written with every
                             hash-map operation counted returns the same
                             results; a firing costs a number of operations
                             bounded by the rule alone, and a run costs at
                             most three for each pair on the initial work
                             list plus a constant for each step
* `INet.Arith.sum_cost`, `INet.Arith.sum_cost_le`
                             adding `m` and `n` on hash maps takes at most
                             81 operations per step, and at most
                             `93 * m + 12 * n + 99` in all
* `INet.Arith.add_correct`, `INet.Arith.run_add`
                             addition, for all inputs: a net whose only
                             adder has the numerals `m` and `n` as arguments
                             reduces in `m + 1` steps to a normal form with
                             the numeral `m + n` on the result port, and the
                             reducer finds it
* `INet.Addition.Config.steps`, `INet.Addition.add_correct`,
  `INet.Addition.Rules`, `INet.Arith.rules`
                             the same in any interaction system that has
                             three symbols with the two rules of addition
                             among its rules, whatever its other symbols
                             and rules: the adder runs for `m + 1` steps
                             and leaves the numeral `m + n`; `Arith` is the
                             case of these symbols and rules only
* `INet.XMach.relabel_rest`, `INet.Steps.relabel`,
  `INet.Net.relabel_normal`, `INet.Arith.carry_rest`,
  `INet.Arith.Expr.rest_embed`
                             a system inside another: a net of the smaller
                             system, relabelled, reduces in the larger one
                             step for step and to the same normal form, so
                             what is proved for the nets of `Arith` holds
                             for them in any system that `Arith` is inside
* `INet.Peano.rules`, `INet.Peano.embeds`, `INet.Peano.add_steps`,
  `INet.Peano.expr_rest`
                             a system with addition, multiplication,
                             copying and erasing: the adder adds in it,
                             and every expression of additions comes out
                             right in it
* `INet.Peano.erase`, `INet.Peano.copy`, `INet.Net.Keeps`,
  `INet.Addition.IsNum.keeps`, `INet.Addition.gone_closed`
                             erasing and copying a numeral, with any other
                             agents in the net: an eraser on the numeral
                             `n` is gone with it after `n + 1` steps, a
                             copier leaves the numeral `n` on both of its
                             ports after `n + 1` steps, and what was away
                             from them is as it was
* `INet.Addition.Adding.run`
                             the adder adds with any other agents in the
                             net and its result wired to any port
* `INet.Peano.mul_correct`, `INet.Peano.Product`,
  `INet.Peano.Multiplying.run`, `INet.Peano.copy_fresh`
                             the multiplier multiplies: a net whose
                             multiplier has the numerals `m` and `n` as
                             arguments reduces, in
                             `(m + 1) * (n + 2) + m * (n + 1)` steps, to a
                             normal form with the numeral `m * n` on the
                             result port; and it does so with any other
                             agents in the net and its result wired to
                             any port, leaving the rest alone
* `INet.Peano.prod_ok`, `INet.Peano.good_prod`, `INet.Peano.prod_rest`,
  `INet.Peano.prod_fair`
                             the nets `Peano.prod m n` are valid for all
                             `m` and `n`; with any number of threads and
                             any schedule, a run of the machine on one
                             that is at rest has made exactly that many
                             interactions and holds the numeral `m * n`,
                             and under a fair schedule it comes to rest
* `INet.Peano.pow_correct`, `INet.Peano.Powering.run`,
  `INet.Peano.power_rest`, `INet.Peano.power_fair`
                             powers: the agent `pow` with the numerals
                             `e` and `b` as exponent and base reduces to
                             the numeral `b ^ e`, in `powCost e b` steps,
                             in any net; on the machine, a run on the
                             net `Peano.power e b` that is at rest has
                             made exactly that many interactions and
                             holds `b ^ e`
* `INet.Peano.Computes2`, `INet.Peano.Computes1`, `INet.Peano.mul_computes`,
  `INet.Peano.pow_computes`, `INet.Peano.fac_computes`,
  `INet.Peano.fac_correct`, `INet.Peano.fac_rest`, `INet.Peano.fac_fair`
                             what it is for an agent to compute a
                             function in any net, stated once; the
                             multiplier and the power are cases, and so
                             is a factorial agent, proved through that
                             statement for the multiplier; on the
                             machine, a run on the net `Peano.facNet n`
                             that is at rest has made exactly `facCost n`
                             interactions and holds `n!`
* `INet.Peano.iter_computes`, `INet.Peano.prim_computes`, `INet.Peano.Combines2`,
  `INet.Peano.add_combines`, `INet.Peano.mul_computes'`,
  `INet.Peano.pow_computes'`, `INet.Peano.fac_computes'`, `INet.Peano.cater_computes`
                             recursion proved once, in two shapes: an
                             agent whose rule on a successor follows a
                             template in it and a combiner computes the
                             recursion, given what it does on a zero and
                             that the combiner combines; the adder is a
                             combiner; the theorems of the multiplier,
                             the power and the factorial follow, with
                             the same costs; a new agent, the lazy
                             caterer, proved by the theorem alone
* `INet.Peano.unary_rest`, `INet.Peano.unary_fair`, `INet.Peano.binary_rest`,
  `INet.Peano.binary_fair`, `INet.Peano.cater_rest`, `INet.Peano.cater_fair`
                             the machine, proved once for every agent
                             that computes, of one or two arguments: a
                             run at rest has made exactly the counted
                             interactions and holds the value; a fair
                             run comes to rest
* `INet.Peano.GExpr.rest`, `INet.Peano.GExpr.fair`, `INet.Peano.GExpr.good`,
  `INet.Peano.Op1`, `INet.Peano.Op2`, `INet.Peano.PExpr.toG_net`,
  `INet.Peano.sum_rest`
                             expressions over any operators that
                             compute, the factorial and the lazy
                             caterer among them, with the guarantees of
                             the expressions of `+`, `*` and `^`, which
                             are a case; the adder alone on the machine
* `INet.Peano.zero1_const`, `INet.Peano.zero2_const`, `INet.Peano.tri_computes`,
  `INet.Peano.tri_rest`
                             any constant on a zero; the triangular
                             numbers, proved from their rules alone
* `INet.Peano.PExpr.rest`, `INet.Peano.PExpr.fair`, `INet.Peano.PExpr.good`,
  `INet.Peano.add_evals`, `INet.Peano.mul_evals`, `INet.Peano.system_sided`
                             every expression built from numerals with
                             `+`, `*` and `^` comes out right on the
                             machine:
                             with any number of threads and any schedule,
                             a run on its net that is at rest has made
                             exactly `PExpr.cost` interactions and holds
                             the numeral of its value
* `INet.Peano.PExpr.run_sound`, `INet.Peano.PExpr.run_complete`
                             such an expression can be run and its
                             result read off the memory: whatever is
                             returned is its value, and with enough
                             actions the value is returned
* `INet.Arith.sum_ok`, `INet.Arith.sum_correct`
                             the nets `Arith.sum m n` are valid for all `m`
                             and `n`, and on each of them the reducer takes
                             `m + 1` steps and leaves the numeral `m + n`
* `INet.Arith.xsys`, `INet.Arith.onePlusOne_normal_form`,
  `INet.Arith.two_plus_three`
                             unary addition defined by data alone: `1 + 1`
                             normalizes to `2`, and `2 + 3` to `5` in three
                             steps

`INet.Comb.system` instantiates the theory with Lafont's interaction
combinators, and `INet.Comb.gg_step`, `INet.Comb.ggOut_normal`,
`INet.Comb.ggOut_conn` and `INet.Comb.ggOut_compact` run a concrete `γ ⋈ γ`
annihilation and compact its result.
`INet.Solo.system` is a system with a same-symbol rule whose right-hand side
is a single agent.

## Representation

A net is a set of live *agents*, each with a symbol, together with a set of
*wire segments* (`link`) between ports and a set of *free ports* (the
interface).  Port `(i, 0)` is the principal port of agent `i`, and
`(i, k + 1)` is its `k`-th auxiliary port.

A wire of the net is a chain of segments.  Its two extremities are *ends*
(ports of live agents, or free ports); the intermediate points are *junctions*:
ports of agents that have already been consumed.  Firing an active pair never
rewires anything: it deletes the two agents, adds the agents of the right-hand
side, and adds segments attached to the auxiliary ports of the two deleted
agents, which thereby turn into junctions.

New agents are named after a fired agent (`child`).  An agent of the
right-hand side that belongs to the side of `a` is named after `a`; one that
belongs to neither side is named after whichever of the two fired agents
comes first in a fixed order on names.  Firing is therefore a function of
the net and of the unordered active pair alone, and the diamond property
holds up to equality rather than up to renaming.

## Scope

* Systems.  A system gives a rule for each ordered pair of symbols, the two
  orientations being mirror images (`System.rule_symm`).  For two equal
  symbols this says that the right-hand side is its own mirror image, which
  is Lafont's symmetry condition.  The mirror image exchanges the new agents
  of the two sides and fixes those owned by neither side.  Nothing is lost
  by this (`Rhs.Lafont.presented`): take a right-hand side with countably
  many agents and no closed wires, given without owners, and any map of its
  agents that keeps symbols and port numbers and keeps the wires when the
  two sides of the interface are exchanged (`Rhs.Lafont`).  Then an agent
  connected to the interface is exchanged with a different agent, and
  exchanged back (`Rhs.Lafont.reach`), and the right-hand side is, up to the
  numbering of its agents, its own mirror image, with those agents owned by
  one side or the other and the remaining ones by neither.  The map need not
  be a bijection.  How the agents of a rule are numbered, and which side
  owns them, does not matter beyond names: two systems whose rules are
  renumberings of each other (`System.Renum`) simulate each other step for
  step, up to copies of nets, and reach normal forms that are copies in the
  same number of steps (`CStep.renum`, `CStep.renum_inv`,
  `System.Renum.normal_form`).  There the first system reduces without
  history, because copies compose only once history is discarded.
  Renumbering is symmetric and transitive (`Rhs.Renum.symm`,
  `Rhs.Renum.trans`), so two presentations of one right-hand side, given
  without owners say, are renumberings of each other (`Rhs.Renum.common`),
  whatever symmetry was used to find them (`Rhs.Lafont.presented_unique`),
  and two systems that present the same right-hand sides reduce alike
  (`System.common_normal_form`).  So Lafont's condition is enough to fix the
  reductions up to names, although a right-hand side without owners is not
  itself a rule of a `System`.  Right-hand sides are not required to be
  reduced.
* Names.  `Net.WF` asks that no identifier in use extends the identifier of
  a live agent (`fresh`).  This constrains names, not shapes: any net can be
  named with one-element identifiers, as in the examples.  Ports are named by
  lists of numbers, so a net has at most countably many of them.
* `Net.WF` says that every end is attached to exactly one segment, every
  point to at most two, and that the wire leaving an end reaches a different
  end.  Preservation of the last property (`Site.wired_fire`) splits a firing
  into three operations on wires: `JointWired.retire`,
  `JointWired.add_matching` and `JointWired.attach`.  Each is proved for two
  abstract wirings at once, which also shows that the pairing of ends after
  a firing only depends on the pairing before it (`Site.joint_fire`).
* History.  Wires that no longer touch any end (the principal wire of a
  fired pair, or a closed loop produced by an annihilation) stay behind as
  inert segments, and consumed ports stay behind as junctions.  They cannot
  take part in any later step, but they are part of the net: equality of
  nets in the first group of theorems is equality of this representation,
  history included.  `Net.ObsEq` and `Net.compact` forget the history, and
  an equality between compact nets is an equality of observations.
* Closed wires.  Segments form a set, and a right-hand side has no way to
  contain a closed wire without ports.  A loop closed by a firing is
  therefore not always recorded as a cycle of segments.  It is recorded as a
  dead component, and `Loops` counts those.  The count is a relation, defined
  for nets with finitely many dead components.  `XNet.runLoops` and
  `HNet.runLoops` compute it for the reductions they perform, by exploring
  the segments around each fired pair and checking what they find.
* Finiteness.  Nothing is assumed finite beyond the arities; the theorems
  hold for infinite nets and for right-hand sides with infinitely many
  agents.  A wire is always a finite chain of segments.
* What `Net.ObsEq` does not forget.  Equivalent nets have the same live
  agents under the same names.  This justifies discarding inert wire history
  and contracting junctions.  It does not justify deleting live agents that
  are disconnected from the free ports, which may still reduce.  Renaming
  live agents is the business of `Renaming` and `Net.Iso`.
* Renamings.  The name of a new agent owned by neither side depends on the
  order of the two names it is derived from, so firing commutes with a
  renaming only up to an extension of the renaming to the new agents.  The
  theorems produce that extension; it agrees with the given renaming on
  every identifier in use (`Step.map`), or on the free ports when history is
  discarded (`CStep.map`, `XNet.run_map`), so a renaming that fixes the
  interface keeps fixing it.  A renaming has to keep apart all identifiers
  in use, junctions included, and keep reserved names out of use
  (`Renaming.fresh`); that is what makes the renamed net well formed.
  `Net.Iso` is a renaming followed by `Net.ObsEq`.  It is symmetric and
  transitive once the history of the first net is discarded (`Net.Iso.symm`,
  `Net.Iso.trans`); a copy without history has the net as a copy
  (`Net.Iso.symm_compact`).  The history has to go because a renaming must
  keep every name in use apart from the reserved ones, and the history of a
  copy may sit on names that the other net reserves: `Net.Iso.not_symm` is
  a copy with one segment of history that has no copy back.  The
  simulation is proved in both directions directly.
* Both nets must be well formed for the bisimulation: an equivalent net
  could otherwise hold an invisible segment on a name reserved for a future
  agent.
* The list reducer is a reference implementation.  It works on lists, so
  lookups are linear, and it searches the agents for an active pair at every
  step.  `XNet.parStep` fires all the active pairs of a round, but by
  folding over a list: it is a strategy, proved to agree with the sequential
  one.  Correctness is stated for inputs that satisfy `XNet.Ok` (the net
  they stand for is well formed and compact).
  `XNet.check` decides that invariant and steps preserve it, so
  `XNet.normalize` needs no hypothesis.  The check is quadratic.
* The hash-map reducer does a number of map operations per step that
  depends on the rule and not on the net, and entries that are no longer
  active stay on the work list until they are reached.  `HNet.runC_cost`
  accounts for both.  What it counts is hash-map operations, one unit each.
  The count belongs to a second definition of the reducer, `HNet.runC`,
  proved to return what `HNet.run` returns; it is not a measurement of
  compiled code.  The list work on the neighbourhood of a pair is not
  counted (its size is bounded by the rule), and a hash-map operation takes
  constant time only in expectation.  Hashing is opaque to the kernel, so
  runs of this reducer cannot be proved by `decide`; the evaluated examples
  use the list reducer, with which it is proved to agree.
* Concurrency.  `Conc` is an interleaving model on nets with history, in
  which a claim sees and takes an active pair in one action.  `Mach` refines
  it to actions on single cells, with private state for each thread and no
  record of what is still to be written other than those private states.
  It is still a transition system, not a program that runs.  Its memory is
  the set of cells of a `Net`: one agent cell for each name and one segment
  cell for each ordered pair of ports.  Actions of different threads happen
  one at a time, so weak memory is not covered.  Which cell a thread reads
  next is a free choice: there are no work queues, and how the threads
  notice that nothing is left to do is not modelled.  The theorems are about
  every schedule (what the machine computes) and about some schedule (that
  it can always go on).  Nothing is proved under a fairness assumption, and
  an unfair schedule can keep threads looking, or giving agents back, for
  ever.
* The program.  `XMach` is Lean code that runs, but it runs one action at a
  time under a schedule given as a list: it simulates the interleavings of
  threads and is not multi-threaded code.  For every schedule it is proved
  safe: every run is an execution of `Mach`.  That a run ends is proved for
  one thread running alone (`XMach.solo_complete`) and for several threads
  that take turns (`XMach.turns_complete`).  A turn (`Turn`) is given by its
  four possible outcomes, each with the run of the program that produces
  it, and `Turn.exists` shows that the program always takes one of them.
  The number of turns is bounded when every thread gets a turn in every
  window of `W` turns (`XMach.turns_bound`): a turn shortens the list of its
  thread or makes a claim.  When attempts of different
  threads overlap, it is proved that the threads never all rest while an
  active pair with a rule is left (`XMach.Live.rest`), so a run that ends
  with every thread at rest has computed the normal form
  (`XMach.exec_rest`), and under every fair schedule the run does come to
  rest (`XMach.fair_complete`): no search along a wire goes on for ever
  (`XMach.Live.seek_bound`), and every action that is not a claim lowers a
  measure of the work left.  When every thread is scheduled in every window
  of `F` actions the number of actions is bounded (`XMach.fair_bound`): the
  window times one pass over the agents, one more for each claim, and the
  writes, where a pass takes at most seven actions for each agent and one
  for each segment.  The threads are not added up, because no thread can
  add to what another still has to do before its next claim; their number
  enters only through the window, which cannot be shorter than it
  (`fair_window_le`).  Segments are counted as the memory holds them, once in
  each direction.  The bound asks that the input lists no agent twice.  It
  is linear in the size of the net for each pass, and for one thread it is
  right up to a constant: on the nets of `Eps.solo_tight` with at least as
  many agents on free ports as pairs, the run takes a ninth of the bound or
  more (`Eps.bound_le`); by the two formulas the ratio tends to a third as
  the agents on free ports grow in number.  Those nets are made for it: the
  agents that lead nowhere are listed first.  Elsewhere the bound can be
  far off.  It comes to 1,878 actions for `2 + 3` on three
  threads scheduled in turn, which are at rest after three hundred, because
  there a thread finds the next pair at the head of its list.  The window
  must enter the bound as a factor: on a net with nothing to reduce, a
  thread that gets every `F`-th action needs `F` times as long for its one
  pass (`Eps.window_tight`), and on a chain of pairs, each of which becomes
  active when the one before it fires, a starved thread makes every claim
  but the first and every pass that follows (`Chain.window_chain`).  The
  second example needs a window longer than a pass over the agents and than
  a look at every pair: the other thread then has time for its own pass,
  which finds nothing, while the first claim waits to be written.  With the
  pairs listed from the last to the first no such room is needed: two
  threads that take turns reach the first pair three actions apart, the one
  behind has passed every other pair by then, finds the first gone and
  rests, and the one ahead, starved from then on, makes every claim, for
  every window of two actions or more (`Chain.window_short`).  On that net
  the bound is at most twelve times the count (`Chain.short_bound_le`), so
  there it is right up to a constant for every window.  On the chain listed
  the other way the count shown falls short of the bound by more than a
  constant when the pairs outnumber the agents that lead nowhere: there a
  pass stops at the first pair left, and the bound charges it for the whole
  net.  The first example holds for any number of threads that the window
  has room for (`Eps.window_many`); the chains have two.  A schedule that is
  fair but has no such window gets no bound.
  The bound counts actions, and an action reads lists.  Running time is
  bounded as well (`XMach.time_bound`), in a model that charges an action
  one unit, one more for each cell its lookups pass, the whole list of
  agents when it takes an agent out or takes the list afresh, and one for
  each cell of a right-hand side it builds; a lookup depends on the cells
  it is charged for and no others (`assoc_take`, `nextSeg_take`).  The
  lookup of a rule counts as part of the unit, and a thread at rest is
  charged nothing.  That bound needs no window and no fairness: the actions
  that are not rests number at most one pass for each thread, one more for
  each claim, and the writes, however the threads are scheduled, and the
  time is that number times the most one action can cost.  On agents that
  lead to free ports, with nothing to reduce, it is right up to a factor of
  twelve for any number of threads (`Eps.time_tight`): each thread reads
  the whole memory once for each agent.  Elsewhere it can be far off: for
  `2 + 3` on three threads it comes to 81,969, and the run in turn takes
  1,213.  With claims it is right up to a constant as well, for one thread
  on the chain listed from the last pair to the first with at least one
  agent that leads nowhere (`Chain.time_chain`, `Chain.time_chain_le`); the
  constant shown there, 168, is crude.  No example has several threads
  that write.
* The indexed memory.  `IMach` is the same program with its lookups done in
  hash maps; it is proved to do, action by action, what the program on
  lists does (`IMach.act_sim`, `IMach.init_sim`), so it makes the same
  passes and the same number of actions.  What changes is the cost of an
  action: a constant, the size of a rule and seven, where on lists it is
  the size of the memory (`IMach.cost_le`).  One action is not constant: a
  thread that has written a right-hand side takes the list of agents
  afresh, and for that it reads the log, drops the dead cells and copies
  the rest.  That happens once for each claim, and the cells dropped were
  paid for when they were written, which gives the second term of
  `IMach.time_bound`.  For `2 + 3` on three threads the bound comes to
  15,755, against 81,969 on lists; the first factor is the same in both,
  so both are as far from a real run as before.  The time is counted by a
  function defined next to the program (`IMach.cost`), in operations on
  the maps and list cells, one unit each; it is not a measurement of
  compiled code, and a hash-map operation takes constant time only in
  expectation.  Building the indexed memory from the net is not counted.
  The simulation needs a net in which no agent is listed twice, since the
  map holds one cell for a name.  Hashing is opaque to the kernel, so no
  run of `IMach` is evaluated as it stands; its time is evaluated on
  lists, by a function proved to return it (`IMach.time_shadow`).  Two
  runs of addition are evaluated so: `2 + 3` on three threads scheduled
  in turn takes 420, where lists take 1,213, and `12 + 12` on one thread
  takes 2,028, where lists take 10,514.  In the second run 737 of the
  2,028 go to taking the agents afresh, thirteen times, and the 313
  actions share the rest.  Run as programs on larger inputs, which the
  kernel has not checked, the same definitions give 48,144 against
  575,666 for `96 + 96`, of which 38,117 for the fresh lists: on
  addition that part comes to dominate, and it grows as the square of
  the input, as the time on lists does.
  Against lists: run for run, the indexed time is at most the agents of
  the net and `C + D + 9` times the time on lists
  (`IMach.time_le_list`), so the index never loses by more than a
  constant.  That it wins is proved on the two families for which lists
  have a lower bound, and only there: on agents that lead to free ports,
  for any threads and any schedule, lists take `(3 * k + 3) / 64` times
  as long or more (`Eps.index_gain`), and for one thread on the chain
  listed from the last pair, `(6 * k + 10 * n + 15) / 1680` times
  (`Chain.index_gain`).  Both constants are crude.  On the first family
  the indexed bound is right up to a factor of ten (`Eps.itime_tight`),
  and for one thread on the chain, with claims, up to thirty-one
  (`Chain.itime_ge`, `Chain.itime_chain_le`).  In general the indexed
  time is the number of actions that are not rests, up to the constant
  `C + D + 7`, and the fresh lists (`IMach.time_ge_work`,
  `IMach.time_le_work`).  That number has a bound for every schedule
  (`XMach.work_le`), right up to a factor of seven for one thread on the
  chain (`Chain.work_chain`, `Chain.work_bound_le`); how far the number
  is from the bound elsewhere is not known, and no lower bound has
  several threads that write.
  There is still no work list of active pairs: a thread walks the whole
  list of agents on every pass.  A work list would have to find the far
  ends of the wires a firing rewires, and in this memory a wire is a
  chain of segments that is only ever added to, so that is a walk too;
  none is attempted here.
* Lazy lists.  `LMach` removes the reading of the log from the indexed
  program: taking the agents afresh costs one.  It is proved to do,
  action by action, what the program on lists does (`LMach.act_sim`,
  `LMach.init_sim`), and its time is at most a constant for each action
  that is not a rest and two for each dead cell dropped
  (`LMach.time_le_work`).  Evaluated on lists by a function proved to
  return it (`LMach.time_shadow`), `12 + 12` on one thread takes 1,394,
  where the indexed memory takes 2,028 and lists 10,514, and `2 + 3` on
  three threads scheduled in turn takes 407, where they take 420 and
  1,213.  Run as programs on larger inputs, which the kernel has not
  checked, the definitions give 10,802 for `96 + 96` against 48,144 and
  575,666, and twice the input takes twice the time.
  What is not proved is a bound on the dead cells dropped.  The log is
  never packed, so it keeps every cell ever written, and a thread that
  walks its whole list passes every cell that was dead when it took the
  list; `LMach.time_le_work` counts those cells and does not bound them.
  The worst case is therefore not shown to be better than that of the
  indexed memory, and the memory grows with the run.  An idle thread
  drops all the dead cells at the front of its list in one action, which
  is not a constant.  The clock ticks at every agent written or taken
  out, in the same action.  As before, the time is counted by a function
  defined next to the program, in operations on the maps and list cells,
  and a hash-map operation takes constant time only in expectation.
* Packing the log.  `PMach` is the lazy program on a memory that drops
  the dead cells of its log as soon as they outnumber the live ones.  It
  is proved to do what the program on lists does (`PMach.act_sim`,
  `PMach.init_sim`).  The log is never more than twice the agents
  (`PMach.log_le`); the packing is paid for by the agents taken out, so
  the time is at most `C + D + 11` for each action that is not a rest and
  two for each dead cell dropped (`PMach.time_le_work`); and the dead
  cells dropped are at most the agents the memory can hold, once for each
  claim (`PMach.skips_le`).  Together these give `PMach.time_bound`,
  which has the shape of the bound of the indexed memory: the worst case
  proved for lazy lists is now no worse than that one, up to the
  constants, and the part for the dead cells is paid only for cells a
  thread in fact walks past.
  On the runs evaluated packing costs a little more than it saves:
  `12 + 12` on one thread takes 1,444, against 1,394 without packing,
  drops no dead cell where the other drops 26, and ends with a log of the
  25 live cells (`Arith.sum12_ptime`, `Arith.sum12_pskips`).  `2 + 3` on
  three threads takes 407 either way.  Run as programs, which the kernel
  has not checked: in the first run the log is packed once, at the last
  claim, for 76, and `96 + 96` takes 11,188 against 10,802.
  What stays unbounded is the map of the deaths: a note is never removed,
  because a thread may still hold a list with the cell in it, so the
  memory as a whole still grows with the run.  The lists the threads hold
  are old logs; that a real memory would have to keep them alive is not
  modelled.  The two counters are kept by the memory and cost nothing in
  the model.
* The ordered memory.  `TMach` does away with the notes of the deaths,
  the clock and the packing: the agents are the entries of a persistent
  ordered map, the live ones only, and a thread that takes the agents
  afresh keeps the map as it finds it.  It is proved to do what the
  program on lists does (`TMach.act_sim`, `TMach.init_sim`).  Every
  action costs at most `C + D + 6`, so the time is that for each action
  that is not a rest and nothing else (`TMach.time_le_work`), and with
  `XMach.work_le` it is bounded for every schedule (`TMach.time_bound`),
  with no term for fresh lists or dead cells.  The memory holds one cell
  for each agent (`TMach.cells_size`) and no thread holds more than the
  memory can (`TMach.todo_le`), so nothing grows with the run but the
  segments, which no memory here removes.
  On the runs evaluated it is not the fastest: `12 + 12` on one thread
  takes 1,444, as on the packing memory and against 1,394 with lazy lists
  alone, and `2 + 3` on three threads takes 451 against 407, because an
  idle thread makes three operations on its map where a list gives the
  next agent for one.  Run as a program, unchecked, `96 + 96` takes
  11,188.
  `TMach.time` counts an operation on a map as one.  `TMach.lgtime`
  charges an operation on an ordered map of `n` entries `lg n`, one more
  than the number of binary digits of `n` (`lg_le`, `lt_pow_lg`): an idle
  thread pays three such on its own map, and taking an agent out or
  writing one pays one on the map of the memory.  Then every action costs
  at most `C + D + 3 + 3 * lg (agents + C * n)` (`TMach.lgtime_le_work`,
  `TMach.lgtime_bound`), where on lists it costs the size of the memory,
  and the charge changes the time by a factor between one and
  `lg (agents + C * n)` (`TMach.time_le_lgtime`, `TMach.lgtime_le_time`).
  With the depth charged the ordered memory is the slowest of the
  memories with maps on the runs evaluated: `12 + 12` on one thread takes
  2,186 against 2,028 indexed and 1,394 with lazy lists, and `2 + 3` on
  three threads takes 688 against 420 and 407; lists take 10,514 and
  1,213 (`Arith.sum12_lgtime`, `Arith.sum23_lgtime`).  Run as a program,
  unchecked, `96 + 96` takes 20,495, against 10,802 with lazy lists,
  48,144 indexed and 575,666 on lists.
  What `lg` charges is the depth of a perfectly balanced tree, and one.
  The tree of `Std.TreeMap` is balanced by weight, and the library proves
  that balance of every map it returns.  From it the depth of the tree is
  proved to be under three times `lg` of its size, and never under `lg`
  less one (`tdepth_lt`, `lg_le_tdepth`).  `TMach.dtime` charges each
  operation the depth of the tree it works on, and one, told from the
  trees the run builds and not from their sizes.  On every run it is
  between `TMach.lgtime` and three times it (`TMach.lgtime_le_dtime`,
  `TMach.dtime_le_lgtime`); every action costs at most
  `C + D + 3 + 9 * lg (agents + C * n)` (`TMach.dtime_le_work`), and the
  time is bounded for every schedule (`TMach.dtime_bound`).
  The kernel evaluates the trees of the library but not its hash maps,
  and `TMach` keeps the names in one.  So the run is replayed on the
  trees alone: `RMach` leaves the hash maps out, finds an agent by going
  through the map of the agents and the neighbours of a port by going
  through the segments, and is proved to keep the trees, the stamp and
  the threads of the run action by action (`TMach.act_strip`,
  `TMach.trace_strip`), so that the time by the depth is the time of the
  replay (`TMach.dtime_replay`).  The largest key is read off the list of
  the map, because the library finds it by a recursion the kernel does
  not unfold (`tmaxKey_eq`).  Evaluated so, `12 + 12` on one thread takes
  2,240, where `lg` charges 2,186, and `2 + 3` on three threads takes
  692, where `lg` charges 688 (`Arith.sum12_dtime`, `Arith.sum23_dtime`).
  Run as a program, unchecked, `96 + 96` takes 21,862 against 20,495 by
  `lg`; its deepest tree is charged 13 where `lg` charges 9.
  The steps of the library's operations are counted on copies.  The
  lookup, the search for the largest key, the insertion and the erasure
  are each written again with a counter of the calls.  The equations are
  those of the library's definitions (`Impl.Const.get?`, `Impl.maxKey?`,
  `Impl.insert!`, and `Impl.erase!` with `glue!`, `minView!` and
  `maxView!`); the results are proved to be the library's (`tgetC_fst`,
  `tmaxC_fst`, `tinsertC_fst`, `teraseC_fst`, the last two through the
  library's own `insert_eq_insert!` and `erase_eq_erase!`); and each is
  proved to make at most one call for each level of the tree, and one
  (`tgetC_snd` and the like), so at most `3 * lg n` (`tsteps_le_lg`).
  `TMach.ctime` charges those counts.  It is at most `TMach.dtime` on
  every run (`TMach.ctime_le_dtime`) and bounded for every schedule
  (`TMach.ctime_bound`).  On the runs evaluated it is 2,007 for `12 + 12`
  on one thread and 573 for `2 + 3` on three threads
  (`Arith.sum12_ctime`, `Arith.sum23_ctime`), under the 2,240 and 692
  that the depth charges, because a search need not run the whole depth
  of the tree.  Run as a program, unchecked, `96 + 96` takes 19,702.
  What a call does besides is one comparison at most and one call of
  `balanceL!` or `balanceR!`, which are not recursive; that is read off
  the library and is not a theorem.  Nor is it a theorem that the
  compiled code of the library makes the calls of these copies: the
  copies have the library's equations and the library's results, and a
  count of calls is not something its functions return.
  That a copy is free rests on the map being a persistent tree, which
  `Std.TreeMap` is, and is not measured.  The map of the names is a hash
  map and is never copied; an operation on a hash map is still counted
  one, which holds on average and not in the worst case.  The time is
  still counted by a function defined next to the program, not measured
  on compiled code.
* Ordered maps alone.  `OMach` is the ordered memory with its two hash
  maps replaced by ordered maps of the library, keyed by names: an agent
  by its name, a port by its index followed by the name of its agent
  (`portKey`), in the order of lists of numbers.  It is proved to stay in
  step with `TMach` action by action (`OMach.act_agree`,
  `OMach.trace_agree`): the same map of the agents, the same threads, and
  the same answer to every lookup.  So it stands for the program on lists
  (`OMach.init_sim`) and comes to rest with the normal form
  (`OMach.fair_complete`, `OMach.fair_bound`).
  `OMach.ctime` counts every call of every operation on the three maps,
  by the counted copies of the library's operations; nothing is counted
  one on the strength of a hash.  The map of the names is no larger than
  the map of the agents and the map of the neighbours has no more keys
  than there are segments (`OMem.Sized`, `OMach.trace_sized`), and the
  segments are bounded along the run (`XMach.wires_le`).  So every action
  costs at most `C + D + 4 + 12 * lg m`, where `m` is what the memory can
  hold, agents and segments together (`OMach.ctime_le_work`), and the
  time is bounded for every schedule (`OMach.ctime_bound`).  The bound
  holds in the worst case, with no assumption on a hash function.
  There is no hash map, so the kernel computes the runs as they stand:
  `12 + 12` on one thread takes 4,343 and `2 + 3` on three threads takes
  948 (`Arith.sum12_otime`, `Arith.sum23_otime`), against 2,007 and 573
  when an operation on a hash map counts one.  Run as a program,
  unchecked, `96 + 96` takes 48,805, against 19,702.
  What a call counts as one is now a comparison of two names.  A name is
  a list of numbers, and comparing two takes time that grows with their
  length, which is not counted; hashing a name has that cost too and it
  was not counted either.  The caveats of the counted copies stand: that
  the balancing functions are not recursive is read off the library, and
  the count is of the calls of the copies, not of compiled code.
* Everything counted.  `OMach.ftime` leaves nothing of an operation on a
  map uncounted in the copies.  A comparison of two names is charged the
  cells it reads (`cmpC`, proved to be the comparison of the library and
  to read at most the cells of the first name and one).  The balancing
  functions are written again with the nodes they build (`balanceLF`,
  `balanceRF`, proved to return what `balanceL!` and `balanceR!` return
  and to build three nodes at most), so that their work is a theorem and
  is not read off the library.  An operation then costs at most five for
  each level of its tree on numbers, and the length of the name and five
  on names.  The names grow: a new agent is named by one cell before the
  name of one of the two that fire, so a name can gain a cell at each
  interaction, and no more (`XMach.act_names`, `XMach.names_le`).  With
  `L` the length of the longest name of the net, every action costs at
  most `C + D + 4 + 12 * (L + n + 6) * lg m` (`OMach.ftime_le_work`), and
  the time is bounded for every schedule (`OMach.ftime_bound`).  The
  factor `L + n` is the price of the names as the model has them; it
  goes with numbered names (`ZMach.ftime_bound`, below).
  The kernel computes the runs: `12 + 12` on one thread takes 11,902 and
  `2 + 3` on three threads takes 2,195 (`Arith.sum12_ftime`,
  `Arith.sum23_ftime`).  Run as a program, unchecked, `96 + 96` takes
  145,921.
  What no theorem here can reach is the compiled code.  The counts are
  those of functions that have the equations of the library's functions
  and return what they return.  That the machine code compiled from the
  library does that much work and no more is a statement about the
  compiler and the machine, and Lean has no model of either.
  It is measured instead, outside the logic.  The last section of this
  file is the program that was timed: compiled with Lean 4.35.0
  (`lean -c`, then `leanc -O2`), it ran addition on one thread on ordered
  maps alone, for `k + k` with `k` from 24 to 768.  The count goes from
  27,888 to 1,622,013 over those inputs, and in three runs the time
  stayed between 15 and 20 nanoseconds for each unit counted.  That is a
  measurement on one machine, of one family of runs; it is not a proof.
* New names.  `XMach.fresh_names` says that a claim never gives a name
  that the program already has anywhere in its state.  It rests on the
  reservation of names in well-formed nets (`Net.WF.fresh`) and on a new
  invariant, that the names a thread holds stay known to the memory
  (`XMach.Wired`).  It is the first step towards naming the agents by
  numbers, which takes the factor `L + n` out of the bound of
  `OMach.ftime_bound`: a numbered program must give each new agent a
  number that no part of the state has, and this is what lets the numbers
  and the names correspond.  The second step is `XMach.act_map`: an
  action does the same on a renamed state, as long as the renaming keeps
  the names in hand apart, so a program that differs only in the names it
  gives can be followed action by action.  What a claim does to the names
  is left out of that theorem.
* Numbered names.  `YMach` is the program on lists that gives each new
  agent a number, one cell, taken from a counter that a claim advances by
  the span of its rule.  `YMach.trace_rel` says that it does what the
  named program does, under every schedule: at each moment there is a
  renaming, one-to-one on the names in the state, that turns the numbered
  state into the named one, and the claims agree.  The renaming changes
  at each claim and is not computed by the program; it exists only in the
  proof.  So the numbered program reaches the normal form up to the names
  (`YMach.fair_complete`), not the same list of names, and its names do
  not grow (`YMach.names_le`).  The counter is one number shared by the
  threads.  With threads that really ran together it would have to be
  advanced atomically, like the claim itself; the model here takes each
  action as one indivisible step.
* Numbered names, counted.  `ZMach` is the numbered program on ordered
  maps alone.  It runs as `YMach` does (`ZMach.trace_sim`), and its time
  with everything counted is bounded without the length of the run in the
  cost of an action (`ZMach.ftime_bound`): where `OMach.ftime_bound` has
  `L + n` it has `max L 1`.  Three things are taken as given in that
  count.  A claim pays one for advancing the counter, and the span of its
  rule is taken as stored with the rule, not computed again.  A cell of a
  name is a number, and reading or comparing one is counted one whatever
  its size; the numbers given grow with the run, up to the counter, where
  the cells of the names that grew stayed small.  And the bound on the
  number of actions that are not rests is the one proved for the named
  program, carried over by the renaming.  On the two runs that the kernel
  computes the numbered program takes 10,999 against 11,902 and 2,126
  against 2,195 (`Arith.sum12_ztime`, `Arith.sum23_ztime`).  Run as a
  program, unchecked, `96 + 96` takes 133,172 against 145,921 and
  `768 + 768` takes 1,444,360 against 1,622,013.  The program timed in
  the last section is still the named one.
* The size of the numbers.  The count takes a number as one unit.  For
  the numbered program that is the count of a machine with words of a
  fixed size, and the size is known before the run: `ZMach.numbers_lt`
  says that the counter, every cell of every name in the state and every
  stamp stay below `2 ^ W` once `2 ^ W` is above `X.top + Sp * n` and
  above the agents of the net plus the bound on the actions that are not
  rests.  `Sp` is the largest span of a rule (`XSys.SpanLe`) and `n` the
  steps to the normal form.  So `W` can be taken logarithmic in those two
  bounds, and in bits the time should be about `W` times the count at
  most.  That is not a theorem here; the next note says what is.
  The index of a port is a number too, a cell of a key of the map of the
  neighbours.  It comes from the net or is fixed by a rule, and it does
  not grow (`YMach.ports_le`).  The bound on the stamps is the bound on
  the work, well above what a run uses: on `12 + 12` the counter ends at
  64 under its bound of 67, and the next stamp at 51
  (`Arith.sum12_numbers`).
* In bits.  `ZMach.btime` is the time of the numbered program with the
  numbers charged by their size.  A comparison of two numbers costs the
  bits of the shorter (`cellBits`), in the operations on the maps and in
  the tests that an action makes on names and ports.  A number made costs
  its bits: the stamp of an agent written, the counter and the numbers of
  a claim.  A call and a node built still count one, so pointers and the
  sizes kept in the nodes are not charged in bits.  What is proved is for
  one operation: on a map it costs at most its count times the bits of
  its key (`ngetB_le`, `tgetB_le` and the like; `OMem.takeB_le`,
  `OMem.putB_le`, `OMem.linkB_le`), and a name of `L` cells below `2 ^ W`
  has at most `L * (W + 1) + 1` bits (`nameBits_le`).  For a whole run,
  under every schedule, the time in bits is at most the count times
  `3 * (lg P + max L 1 * (W + 1) + 1)` (`ZMach.btime_le_ftime`), and so
  it is bounded before the run (`ZMach.btime_bound`).  `P` bounds the
  indices of the ports of the net and of the rules, and `2 ^ W` is above
  the bound on the counter one claim further and above the bound on the
  stamps.  The three is slack: a test that an action makes is paid from
  the unit of the action, and a claim pays two numbers for a segment.
  The bound is far above what a run takes, as the bound on the count is.
  On addition both are closed formulas in the two numbers and the number
  of threads (`Arith.sum_ztime`, `Arith.sum_btime`): for `12 + 12` on one
  thread they give 7,028,955 and 421,737,300.
  The kernel computes the two runs: 28,984 bits for
  a count of 10,999, and 4,220 for 2,126 (`Arith.sum12_btime`,
  `Arith.sum23_btime`).  Run as a program, unchecked, `96 + 96` takes
  474,055 bits for a count of 133,172 and `768 + 768` takes 6,549,085 for
  1,444,360: about 3.6 and 4.5 bits for each unit, where the counter ends
  at 484 and at 3,844, numbers of 9 and 12 bits.
* One thread.  For one thread the general bound on the work is `n + 1`
  passes, each as long as a pass over every agent can be.  A pass can be
  that long when the pair is the last that the thread tries, and nothing
  here shows that the general bound can be made much smaller for one
  thread.  On addition the passes are short, and the run is followed
  action by action for every size.  After a claim is written the single
  thread is the program started afresh on the memory as it is
  (`XMach.single_claim`, `XMach.restart`), so a run is a sequence of
  rounds.  A round is counted for any system (`Works.claim_direct`,
  `Works.claim_via`), given what the lookups of the thread return.  For
  addition an invariant of the memory gives those lookups at every round
  (`Arith.Start`, `Arith.Steady`): the first round takes sixteen
  actions, each later one seventeen, and the last, with the zero, nine.
  The memory is described exactly through the rounds (`Arith.Hist`,
  `Arith.Final`): its agents in order, and its segments as those of the
  net and those each round wrote, none being removed.  From that the
  last pass is read off entry by entry (`Arith.Final.pass`): a thread
  gives up on a successor of the result after four actions, walks from
  the top of the second argument down every adder the rounds made
  before it stops, and gives up on every other entry after three.  So
  one thread adds `m` and `n` in exactly `22 * m + 3 * n + 13` actions
  (`6 * n + 13` when `m` is zero), for every `m` and `n`
  (`Arith.solo_work`).  The law is that of this program on these nets,
  with the agents listed in this order; it is not a law of addition, and
  another order of the list gives other passes.  The actions are not
  charged alike.  By its state an action is charged operations on the
  maps of agents, up to four, and on the map of segments, up to two
  (`XThread.opsA`, `XThread.opsW`), and the same runs, followed with
  that charge (`Opers`), come to `23 * m + 5 * n + 18` operations on the
  maps of agents and `23 * m + 2 * n + 10` on the map of segments
  (`10 * n + 18` and `4 * n + 10` when `m` is zero; `Arith.solo_ops`).
  The charge is a bound, by the state alone: one of each kind for every
  segment followed, where one lookup is often enough.  The count of the
  numbered program is then at most fifteen for each action and, for
  each operation, the cost of one on its own tree at full depth, the
  trees of agents by the agents that the memory can hold and the tree of
  segments by the segments (`ZMach.ftime_le_ops`,
  `Arith.solo_ztime_ops`), and at least one for each action
  (`ZMach.work_le_ftime`, `Arith.solo_ztime_ge`); the bits follow
  (`Arith.solo_btime_ops`).  For `12 + 12` that is 313 actions, 354
  operations on trees of at most 53 agents and 310 on a tree of at most
  206 segments, so between 313 and 107,889 counted, and at most
  6,473,340 bits; four operations for every action on trees of 379
  entries gave 267,615 and 16,056,900 (`Arith.sum12_solo`); the bounds
  for every schedule are 7,028,955 and 421,737,300; and the run takes
  10,999 and 28,984.  For `1000 + 1000`, a size not computed here, it is
  25,013 actions, 28,018 and 25,010 operations, at most 14,809,557
  counted and 1,421,717,472 bits.  What is left of the gap is the cost
  of one operation, which is charged as on a tree as deep as its size
  allows, with a full comparison at every level.
* Two threads.  A second thread can make the program slower, and by any
  factor.  After a claim a thread starts again on the whole list of
  agents, the newest first.  A thread that claims the next pair from an
  older list first finds its first agent gone, and then passes every
  successor of the result that its list holds, four actions each, before
  it comes to the successor of the pair.  Under a schedule that lets the
  two threads claim in turn, each running alone until its claim is
  written (`Arith.altSched`), the block that claims the pair numbered `j`
  takes `4 * j` actions and a constant, and on the net for
  `(m + 2) + n` the first `2 * m * m + 21 * m + 33` actions are all work
  (`Arith.two_threads_quadratic`), where one thread adds in
  `22 * m + 3 * n + 57` actions in all.  The same holds for any schedule
  that begins so (`Arith.two_threads_any`).  So the bound for every
  schedule, which is quadratic for addition, cannot be made linear for
  two threads; one thread is linear because it finds the next pair at
  the head of its own new list.  The schedule is chosen against the
  program: a thread runs alone for up to `4 * m + 19` actions.  When
  threads act in turn, the first thread first, the work is linear,
  whatever the second argument and for any number of threads that the
  first argument is long enough for: on the net for `(m + 1) + n`, with
  `k + 1` threads, `k + 3 ≤ m` and `20 * k ≤ 3 * m + 3 * n + 22`, at most
  `116 * m + 33 * n + 267` actions and `48 * m + 15 * n + 85` for each of
  the `k` other threads are not rests (`Arith.threads_any_second`), and
  the schedule is free after the first `(k + 1) * (17 * m - 1)` actions.
  The other threads run ahead of the first and read each agent of their
  lists while the pair above it is not yet written, so they make no
  claim while the first thread makes all its claims but two; the last two
  claims are paid by the measure of the general bound taken at that
  moment (`XMach.work_tail`), which is why the constants are large.  When
  the second argument is short, `48 * n + 99 ≤ 221 * m`, or long,
  `221 * m + 51 * k + 281 ≤ 48 * n`, the other threads never claim, and
  the work is that of one thread and at most `4 * m + 3 * n + 15` more for
  each of them, and no less (`Arith.threads_round_robin`): with a short
  one every thread passes the zero of the first argument before the last
  pair is ready, with a long one every thread comes to it after the first
  thread has taken it (`Arith.solo_gone_zero`) or the last adder.  The actions of a thread
  up to that zero are counted exactly up to one: three on each successor
  of its chain and each agent of the second argument, one on the first
  adder, and a walk from the top of the second argument with one hop for
  each round written when the thread gets there (`Arith.solo_link`,
  `Arith.solo_no_link`).  A thread that finds that zero reads on to the
  last adder when the segment between them is written
  (`Arith.solo_no_link3`), and gives up when the adder is gone
  (`Arith.solo_gone_adder`).  That leaves about `k + 3` values of `n` for
  each `m`, whatever `m` is: those where a thread can find the zero, the
  segment and the adder all in memory, and so take the pair.  In the runs
  computed with two threads it does so for each of these sizes, scans all
  the agents again, and the work exceeds that expression by about one such
  pass (two threads on `21 + 94`: 1,496 against 1,134; on `21 + 93` and
  `21 + 98` the bound holds and is proved).  For two threads the race is
  followed to its end, to the action (`Arith.two_threads_exact`): until
  the second thread is ready to take the zero, which is when each thread
  has made `17 * m + 11 + d` actions with `d` up to nine, the run is that
  of one thread alone with a reader beside it
  (`Arith.two_threads_entry`); from each of the ten moments one thread
  takes the pair within six actions of each, the second thread in nine of
  them, and both then pass over the agents that are left, in a memory
  that stays as it is.  No thread is at rest before that last pass, so
  every action counts, and the work of the whole run is exactly
  `Arith.raceWork m n d`: from `44 * m + 6 * n + 52` for `d = 0` to
  `44 * m + 6 * n + 68` for `d = 9`, and `39 * m + 3 * n + 60` for
  `d = 8`, where the first thread keeps the pair and the second has two
  entries left to pass.  Which `d` a size has is proved too, and with it
  the work of two threads for every size (`Arith.two_threads_total`, `m`
  from four on).  The segment from an adder to the next is the first that
  a round writes, at its ninth action (`Arith.solo_link8`,
  `Arith.solo_no_link8`), so the walk of the second thread has exactly
  `(3 * m + 11) / 16` hops, and the thread comes to the zero of the first
  argument after exactly
  `Arith.twoAt m n = 3 * m + 3 * n + 1 + (3 * m + 11) / 16` actions
  (`Arith.two_reader_at_zero`).  The race takes place when that number is
  `17 * m + 7 + d` with `d` up to nine, and then the work is
  `raceWork m n d` (1,496, 1,506, 1,519 and 1,530 on `21 + 94` to
  `21 + 97`, where `d` is 0, 3, 6 and 9; 285 on `5 + 23`, where `d` is
  8).  Otherwise the second thread only reads, and the work is that of one
  thread and the actions of the second before it rests: `twoAt m n + 7`
  when it passes that zero before the segment to the last adder is
  written, `twoAt m n + 8` when it finds the last adder gone,
  `twoAt m n + 5` when it finds the zero gone (1,105 on `21 + 93`, 1,136
  on `21 + 98`).  In every case at most `44 * m + 6 * n + 68` actions are
  not rests (`Arith.two_threads_race`).  For any number of threads the
  count is exact outside the race (`Arith.threads_total`): with
  `k + 1 ≤ m` and `20 * k ≤ 3 * m + 3 * n + 21`, the thread numbered
  `t + 1` comes to the zero of the first argument after exactly
  `Arith.turnAt m n t = 3 * (m - t) + 3 * n + 1 + (3 * (m - t) + 11) / 16`
  actions; if for no thread that number is `17 * m + 7` to `17 * m + 16`,
  every thread after the first only reads and rests after exactly
  `Arith.turnRest m n t` actions, its `t + 1` top successors costing one
  each, and the work is that of one thread and those actions (300 for
  three threads on `7 + 9`, 580 for four on `6 + 31`).  For three threads
  the race is exact when the second thread is in it and the third is
  already past that zero, `turnAt m n 1 ≤ 17 * m + 6`
  (`Arith.three_threads_race_first`): the third thread has one action left
  at most, which changes nothing, and the work is that of the race of two
  threads and `turnRest m n 1` (612 on `7 + 30`).  When the third thread
  is in the race the second comes to that zero three or four actions
  later.  If that is after the ten moments, `17 * m + 17 ≤ turnAt m n 0`,
  and then the third thread is ready to take the zero when the first is
  past its last round, `d` from 6 to 9, the count is exact
  (`Arith.three_threads_race_third`): the second thread reads on to the
  last adder, finds it gone and reads to the end of its list, eight
  actions after it came to that zero, and the work is `raceWork m n d`
  for the first and the third thread and `turnAt m n 0 + 8` for the
  second, one more when the first thread keeps the pair (653 on
  `7 + 33`, 594 on `8 + 38`).  If the second thread too comes to that
  zero at one of the ten moments, it has just popped it or is about to
  when the third takes it, and it does the same: the work is given by the
  same expression (`Arith.three_threads_race_both`; 624 on `7 + 31`).
  So for three threads in turn the work is known to the action for every
  size, with `m` from four on and `19 ≤ 3 * m + 3 * n`
  (`Arith.three_threads_total`).  For four threads the race is exact
  when the fourth thread is in it, `turnAt m n 2` from `17 * m + 7` to
  `17 * m + 16` (`Arith.four_threads_race_last`): the fourth thread and
  the first race as two threads would; the third, three or four actions
  behind the fourth, reads on to the last adder and finds it gone; the
  second, three or four actions behind the third, finds the zero gone.
  The work is `raceWork m n d`, `turnAt m n 1 + 9` and `turnAt m n 0 + 5`,
  and two more when the first thread keeps the pair (752 on `7 + 32`, 744
  on `8 + 39`).  The ten cases of the race are proved with any number of
  threads reading between the two (`Arith.race_k_d0` to
  `Arith.race_k_d9`), each thread being shown to read in the five
  memories the race goes through (`Arith.RaceViews`, `Arith.Beside`).  In
  the runs computed, with up to six threads, the thread that races is the
  first to come to that zero during the ten moments; the thread that
  comes next pays four actions for the zero, those after it one, and
  those that came before the ten moments three.  The last of these is
  proved for any thread: a thread that comes to that zero before the ten
  moments only reads, whatever the threads before it do, and adds exactly
  `turnRest m n t` to their work (`Arith.threads_early_last`).  Its first
  actions are those it makes beside one thread alone, because no other
  thread can write before it has passed the zero of the second argument,
  and its top successors are gone for good by then (`Arith.trace_gone`).
  So four threads in turn are exact for every size, with `m` from four on
  and `39 ≤ 3 * m + 3 * n` (`Arith.four_threads_total`; 725 on `7 + 30`),
  and so are five threads or more when the fifth passes that zero before
  the race (`Arith.threads_beyond_four`; 984 for five threads on
  `8 + 36`, 1,956 for six on `14 + 64`).  The rest is proved too.  A
  thread that is still on the second argument when the race starts reads
  on in each of the five memories the race goes through
  (`Arith.LateMem`, `Arith.beside_late`) and finds that zero gone.  So
  with any number of threads, the last of which races, the work is
  `raceWork m n d`, `turnAt m n j + j + 8` for the thread that comes next
  and `turnAt m n t + t + 5` for those after it, and one more for each of
  these threads when the first thread keeps the pair
  (`Arith.threads_race_last`).  With the threads that pass early this
  gives the work of `k + 1` threads in turn for every size,
  `Arith.allWork m n k`, with `m` from four on, `k + 1 ≤ m` and
  `20 * k ≤ 3 * m + 3 * n + 21` (`Arith.threads_exact`): 1,014 for five
  threads on `8 + 38`, 1,284 for seven on `8 + 38`, 2,258 for eight on
  `13 + 60`.  One more thread never saves work (`Arith.threads_more`):
  under the conditions for `k + 2` threads the work grows by at least
  `turnAt m n k`, the actions that bring the new thread to that zero, and
  by at most the work of one thread less two; the second bound is reached
  by two threads on `6 + 28`, 456 against 229.  A thread that is not in
  the race adds exactly `turnRest m n k` (`Arith.allWork_succ_out`).  So
  `k + 1` threads in turn do at least the work of one thread and
  `3 * n + 4` for each other thread, and at most `k + 1` times the work
  of one less two for each other thread (`Arith.threads_bounds`).  The
  time is counted in rounds (`Arith.Rounds`).  Outside the race the run
  of `k + 1` threads is at rest after exactly `soloWork (m + 1) n`
  rounds, the actions of one thread alone, so the other threads save no
  time and their actions are pure overhead (`Arith.threads_overhead`).
  In the race the runs computed, with two to five threads, end sooner
  than one thread by 9, 8, 7, 6, 4, 4, 3, 2, 0 and 0 rounds for `d` from
  0 to 9.  For two threads that is proved
  (`Arith.two_threads_race_rounds`): each case of the race gives what the
  first thread and the last still do after its five actions
  (`Arith.RaceEnd`), and the run ends when the one with more to do is at
  rest.  So two threads in turn take exactly `Arith.twoRounds m n` rounds
  for every size with `m` from four on (`Arith.two_threads_rounds`), never
  more than one thread and at most nine fewer
  (`Arith.two_threads_rounds_bounds`): 211 rounds on `6 + 25`, where one
  thread takes 220.  The same holds for any number of threads
  (`Arith.threads_rounds_exact`): the threads between the two that race
  are at rest before them (`Arith.RaceEnd.rounds`), and so are the
  threads that passed that zero early
  (`Arith.threads_early_many_rounds`), so `k + 1` threads in turn are at
  rest after exactly `Arith.allRounds m n k` rounds, under the conditions
  of `Arith.threads_exact`: the rounds of one thread alone, less
  `raceSave d` when a thread races.  More threads in turn therefore save
  nine rounds at most and cost none (`Arith.threads_rounds_bounds`),
  while each of them adds at least `3 * n + 4` actions of work.  On a net
  with two additions side by side (`Arith.twoSums`) threads do save time.
  One thread takes `Arith.twoSolo` rounds, those of each addition alone
  and one more pass over what the first has left, and that is proved for
  every size with `m` and `m'` from one on (`Arith.two_sums_solo`).  The
  proof sees each addition inside the larger memory (`Arith.Looks`): the
  cells with its tag are the net alone, whatever the memory holds beside
  them, so its rounds are those of the net alone
  (`Arith.Looks.rounds_all`), and a thread that only reads passes its
  cells as it does on the net alone (`Arith.Looks.pass`,
  `Arith.pass_two`).  For two threads the first stretch of the run is
  proved for every size with `m` at least two, outside the race for the
  last pair of the first addition.  Every action of a thread on a net
  inside a larger memory is its action on the net alone
  (`Arith.Looks.act`, `Arith.Inside.solo`), so while the second thread
  reads its way through the first addition the run is the run of two
  threads on that addition alone (`Arith.beside_stretch`,
  `Arith.two_sums_stretch`).  The second thread then comes to the second
  addition, untouched, claims its first pair in round
  `turnRest m n 0 + 3` (`Arith.two_sums_second_claim`) and has made its
  first interaction after round `turnRest m n 0 + 14`
  (`Arith.two_sums_second_reload`), where one thread alone claims that
  pair with its action `22 * m + 3 * n + 39`
  (`Arith.two_sums_one_claim`): a head start of `18 * m + 20` rounds at
  least (`Arith.head_start`).  There the stretch ends: from its reload
  on, a thread loads the cells of both additions.  The first collision
  is computed, not proved: with `b` the round in which the second thread
  comes to the second addition, if `b % 17` is at most eight the first
  thread next reloads with the new adder of the second addition at the
  head of memory and goes for its pair, if it is nine it finds only the
  new successor there, and otherwise the second thread reloads with the
  adder of the first addition at the head (`Arith.crossLaw`, checked by
  the kernel on the seventeen phases for `6 + n` beside `2 + 0`,
  `Arith.first_collision_checked`).  The saving of time itself is
  computed, not proved for every size: two threads are at rest sooner
  than one thread, by two rounds at least, for `m` and `m'` up to two
  and `n` and `n'` below three by the kernel
  (`Arith.two_sums_two_threads`), and for `m`, `m'`, `n` and `n'` up to
  five in the runs computed; on two
  equal additions up to `10 + 15` they take between 64 and 98 hundredths
  of the rounds of one thread, and more work (`Arith.two_sums_4_3`: 174
  rounds against 254, 327 actions against 254).  Their rounds follow no
  simple law: a thread reloads the whole memory after each interaction
  and takes pairs of either addition; on `6 + 10` twice the first thread
  fires five pairs of each addition and the second two of each.  A proof
  of the rounds of two threads would need what follows each of the
  seventeen first collisions, and the races after them, which are not in
  this development.  What is proved for every size is a limit on the saving.
  An interaction costs the thread that claims it sixteen actions,
  whatever the other threads do: four to read the pair and take its first
  agent, one to claim, ten to write what the rule of a successor makes,
  one to reload; the rules of zero write two segments only and cost
  eight (`Arith.rule_cost`, `Arith.act_cost`).  So a run that ends at
  rest, with any number of threads and any schedule, has done sixteen
  actions of work for each claim, less eight for each adder of the net
  (`Arith.rest_cost`); on two additions it has made `m + m' + 4` claims
  (`Arith.two_sums_claims`, from the fact that two well-formed nets side
  by side are well formed, `Arith.beside_wf`), so `c` threads in turn
  need `16 * (m + m' + 3) / c` rounds at least
  (`Arith.two_sums_rounds_ge`) and two threads `8 * (m + m' + 3)`
  (`Arith.two_threads_two_sums_ge`): 104 on `6 + 10` twice, where one
  thread takes 415 and two threads take 288 in the run computed.  The
  limit counts the interactions only, not the reading of the lists, and
  is far below the rounds computed.  For one family the rounds of two
  threads are proved exactly, and with them that threads save time: on
  `1 + n` beside `1 + n'` with `n` at least seven, two threads take
  `6 * n + 3 * n' + 50` rounds, thirty fewer than one thread
  (`Arith.ones_two_threads`, `Arith.ones_saving`).  There the threads
  never go for the same pair.  The first thread makes the two
  interactions of the first addition and passes what they leave; the
  second reads its way past the first addition, whose adder and zero are
  gone when it comes to them (`Arith.reader_ones`, which is where `n`
  must be seven at least), makes the two interactions of the second
  addition while the first thread still reads on the first
  (`Arith.claim_rounds_read`, `Arith.write_rounds_read`,
  `Arith.zero_rounds_read`), and passes the whole memory; the first
  thread comes to the cells of the second addition when it is done, and
  is at rest before the second thread.  One thread comes to the second
  addition after the twenty-five rounds of the first and a pass of
  `3 * n + 10` actions over what they leave; the second of two threads
  comes to it after `3 * n + 5` rounds of reading, while the first
  addition is being made: thirty rounds sooner.  The same is proved
  for every first argument whenever each addition is done before the
  other thread comes to it (`Arith.apart_two_threads`).  On
  `(m + 1) + n` beside `(m' + 1) + n'` with `m` at least one, the second
  thread must come to the second addition after the `17 * m + 25` rounds
  of the first (`17 * m + 26 ≤ turnRest m n 0`), and the `17 * m' + 25`
  rounds of the second must end before the first thread has passed what
  the first addition left
  (`turnRest m n 0 + 17 * m' + 24 ≤ 22 * m + 3 * n + 35`).  The rounds
  are then `turnRest m n 0 + 5 * m + 3 * n + 22 * m' + 3 * n' + 44`, and
  the saving is `22 * m + 3 * n + 36 - turnRest m n 0`, at least
  `18 * m + 23` and at least `17 * m' + 25` (`Arith.apart_saving`): the
  second thread makes every interaction of the second addition, one
  round of seventeen after another (`Arith.later_many_read`), while the
  first thread only reads.  Both conditions hold when `n` is at least
  `5 * m + 7` and `m'` is at most `m`, and there the rounds have a
  closed form that covers `m = 0` as well (`Arith.apart_family`): one
  thread takes `27 * m + 6 * n + 22 * m' + 3 * n' + 80` rounds, two take
  `8 * m + 6 * n + 22 * m' + 3 * n' + 50 + (3 * m + 11) / 16`, at least
  `18 * m + 29` fewer.  So `6 + 32` twice takes 613 rounds with one
  thread and 489 with two (`Arith.twice_family`).  The saving grows with
  the first argument of the first addition only: both threads still read
  the whole memory between interactions, and the reading is most of the
  time.  Outside these conditions (a short second argument of the first
  addition, or a second addition with the longer first argument) one
  thread comes to an addition while the other works on it.  With a
  short second argument the runs computed show collisions again; with a
  longer first argument of the second addition the three runs computed
  still take the rounds of the formula.  Nothing is proved of either
  beyond the first collision and two limits: the one above, and a second
  that counts the reading as well.  A thread takes an entry off its list with
  every action that is not toward a claim, and when it reloads the list
  it has the whole memory to read again.  A rule of the addition writes
  as many successors as it takes, so the successors in memory and those
  the threads hold stay as many as at the start (`Arith.act_succs`); a
  thread holds one at most (`Arith.act_held`); so the memory never has
  fewer agents than the net has successors less the number of threads.
  With any number of threads and any schedule, then, a run that ends at
  rest has done fifteen actions for each claim, less eight for each
  adder, and for each thread as many as the net has successors less the
  number of threads (`Arith.act_cost2`, `Arith.rest_read`).  On two
  additions `c` threads in turn need
  `(15 * (m + m') + 44) / c + (m + n + m' + n' + 2 - c)` rounds at
  least (`Arith.two_sums_rounds_read`), and more than
  `m + n + m' + n' + 2 - c` whatever `c` is
  (`Arith.two_sums_rounds_floor`): more threads lower the first part and
  not the second.  On `6 + 32` twice that is 171 rounds for two
  threads, where they take 489, 121 for four and 73 for sixteen.  That
  limit counts one action for each entry read.  For the successors of
  the second arguments it is three: such a successor is never one of a
  pair, under any schedule (`Arith.two_sums_snd_forever`), and a thread
  that reads it follows its wire before it reads the next entry.  The
  proof gives every port a side (`Arith.XP`): the principal ports of the
  adders and of the zero of the first argument, and the ports of the
  successors of the first argument, on one; every other port on the
  other.  Every segment of the net joins two ports of one side
  (`Arith.sum_color`), and so does every segment a rule writes
  (`Arith.rule_color`).  A thread that follows a wire stays on the side
  it started from, and a pair has an adder, so both its principal ports
  are on the first side, where no successor of a second argument has its
  own; every action of every thread keeps this (`Arith.act_inv`,
  `Arith.trace_ok`).  With three actions for each of those successors
  (`Arith.act_cost3`, `Arith.rest_read3`), `c` threads in turn on two
  additions need
  `(15 * (m + m') + 44) / c + (m + m' + 3 * (n + n') + 2 - c)` rounds
  at least (`Arith.two_sums_rounds_read3`,
  `Arith.two_sums_rounds_floor3`): 299 for two threads on `6 + 32`
  twice, where they take 489, 249 for four and 201 for sixteen.  What is
  left between that limit and the rounds proved is the reading again: a
  thread reloads the memory after an interaction and reads it once
  more, and that limit counts one reading for each thread.  A second
  reading is proved for `m + 2` threads or fewer in turn.  Each of them
  starts with the `n` successors of the second argument of the first
  addition before the cells of the second, and a list reloaded while the
  second addition is untouched has them there again; three of its own
  actions go to each (`Arith.act_lam`, on a measure of what a thread has
  still to do that no action of its own lowers by more than one, and
  `Arith.rr_step`, which counts the actions of each thread in turn).  So
  in the first `3 * n` rounds no thread comes to a cell of the second
  addition; a thread that starts from a cell of the first net stays in
  it, because no segment joins the two nets; and the cells of the second
  addition are all in memory, in place (`Arith.act_phase1`,
  `Arith.phase1`, `Arith.two_sums_untouched`).  Every claim uses up a
  successor or the zero of a first argument (`Arith.act_first`,
  `Arith.trace_first`); the first addition has `m + 2` of them at most
  and a run at rest has made `m + m' + 4` claims, so some thread claims
  after those rounds.  It then writes, reloads, and has the whole memory
  to read before it rests (`Arith.late_floor`).  The rounds and the
  threads are together at least `6 * n + 3 * n' + m + m' + 4`
  (`Arith.two_sums_rounds_late`), which has the terms in `n` and `n'` of
  the rounds proved for the family: on `6 + 200` twice two threads take
  2,001 rounds and cannot take fewer than 1,812.  On `6 + 32` twice it
  gives 300, one more than the limit before: there the interactions
  weigh more than the reading.  The interactions of the second addition
  are counted next.  They all come after the first `3 * n` rounds, and
  over any stretch of a run sixteen actions go to each claim, but for
  what the threads had put toward claims when the stretch began, four
  actions each at most, for eight for each adder, and for what they owe
  at its end, eleven each at most (`Arith.seg_cost`, `Arith.trace_bnd`).
  So the last claim comes `(16 * (m' + 2) - 15 * c - 17) / c` rounds or
  more after the first stretch, and its thread reads the memory after it
  (`Arith.claim_rest`, `Arith.late_floor2`).  With `c` threads,
  `c * (6 * n + 3 * n' + m + m' + 4) + 16 * (m' + 1) ≤ c * (R + c + 16)`
  (`Arith.two_sums_rounds_late2`), and for two threads
  `6 * n + 3 * n' + m + 9 * m' ≤ R + 6` (`Arith.two_threads_late2`):
  332 rounds on `6 + 32` twice, where they take 489, and 1,844 on
  `6 + 200` twice, where they take 2,001.  This count shares the
  interactions among the threads, sixteen actions for all of them
  together; in the runs of the family one thread makes them all, at
  seventeen rounds each, and that is what is left between the limit and
  the rounds proved.  Looking at one addition alone would not make this
  count better for two threads: by hand, an interaction needs a segment
  that the one before writes as its fifth cell, and then three actions
  more, so two interactions of one addition are some eight rounds apart,
  which is what sixteen actions shared by two threads come to.  A proof
  of that would help from three threads on; it is not in this development.  The
  limit does hold for more threads.  A thread numbered above `m + 1`
  starts further in the first addition, with fewer of the successors of
  its second argument before the second addition, so with `c` threads
  up to `m + n + 2` the first stretch is shorter by three rounds for
  each thread beyond `m + 2` (`Arith.two_sums_init_pre3`,
  `Arith.two_sums_untouched2`, `Arith.two_sums_rounds_late3`): on
  `6 + 32` twice eight threads take 458 rounds in the run computed and
  cannot take fewer than 287, and sixteen take 399 and cannot take fewer
  than 249.  The first stretch itself does not need the threads to take
  turns: under any schedule, as long as every action is made by a thread
  that had made fewer than `3 * n` of its own, the cells of the second
  addition are all in memory, in place (`Arith.phase1s`,
  `Arith.two_sums_untouched_any`).  The rounds proved for the family
  were not carried to a second addition with the longer first argument,
  where three computed runs give the same formula.  By hand, the first
  thread then reads cells of the second addition while the second thread
  is still at work on them, and the formula holds only when it meets
  cells that are gone or comes to the pair at a moment when it cannot
  take it; which of these happens turns on where the two threads are in
  the seventeen rounds of an interaction, and no condition came out
  that is worth a proof.  What is proved for those sizes, and for every
  number of threads and every schedule, is what the memory holds.  A
  thread that starts from an agent of one net stays in it: the port it
  has come to, the pair it has found or holds, and what it has to write
  are in the net of that agent, and no segment written joins the two
  nets (`Arith.act_tag`, `Arith.trace_tag`, `Arith.two_sums_apart`).
  So each net keeps its own successors, in memory or held
  (`Arith.act_succs1`, `Arith.two_sums_succs_each`), and in each net the
  zeros are as many more than the adders as at the start, because a rule
  that ends an adder ends a zero (`Arith.rule_census`,
  `Arith.act_census`, `Arith.trace_census`).  The adders are as many
  more than the zeros of first arguments as at the start
  (`Arith.act_zf`, `Arith.trace_zf`).  A run at rest has made a claim
  for every cell of the first arguments, and each claim uses one up, so
  none of those cells is left, and so no adder
  (`Arith.two_sums_rest_first`, `Arith.two_sums_rest_adders`).  At rest
  the memory then holds `m + n` successors and a zero in the first net,
  `m' + n'` successors and a zero in the second, and no other agent
  (`Arith.two_sums_rest_census`, for first arguments of one or more).
  This counts the agents.  How they are wired is read off the run of
  one thread.  Runs that end at rest hold the same net, whatever the
  numbers of threads and the schedules (`Arith.rest_mem_eq`, from
  `MRun.confluent`), so it is enough to look at the memory one thread
  leaves.  For each addition that memory holds the cells that the rounds
  on the addition alone leave (`Arith.two_sums_solo_final`).  The memory
  one thread leaves on one addition has the numeral on its free port,
  because it is the normal form (`Arith.sum_rest_num`,
  `Arith.solo_final_num`).  And a numeral of a net whose cells are in a
  larger memory under a tag is a numeral of that memory: the segments of
  the net are there, and an agent or a free port with the tag is one of
  the net, so the ends of its wires are ends and the points between are
  not (`Arith.Within`, `Arith.Within.isNum`).  So a memory at rest has
  the numeral `m + n` on the free port of the first net and `m' + n'` on
  that of the second (`Arith.two_sums_rest_num`, for first arguments of
  one or more), and under a schedule in which every thread keeps being
  scheduled the run does come to rest (`Arith.two_sums_fair`).  A
  numeral is a zero under successors joined by wires, and a wire is any
  chain of segments: the memory keeps the segments of earlier rounds,
  so `Arith.readNat`, which follows single segments, does not read it.
  The first arguments of one or more came from the run of one thread on
  two additions, which was written for that case.  It is not needed.
  Let one thread alone bring a net `A` to rest and a net `B` to rest,
  and let a new pass over what it leaves of `A` only read.  On the two
  nets side by side the thread does on the first what it does on `A`
  alone, action for action and claim for claim, because the cells of
  `A` come first in its list (`Arith.Inside.works`); when it has
  finished there it is idle, so the memory is a net that the start
  reduces to (`Arith.works_steps`).  The same net with the cells of the
  second net listed first is a memory on which a thread does what it
  does on `B` alone (`Arith.swapped`, `Arith.swapped_toNet`,
  `Arith.swapped_inside`), then passes the cells of the first, reading
  only, and rests; and a memory at rest is a normal form
  (`Arith.works_normal`).  So the two nets side by side reduce, in as
  many steps as the two runs have claims, to a normal form that holds
  what each run leaves (`Arith.beside_normal`).  For an addition the
  run of one thread and its last pass are known for every first
  argument, zero included (`Arith.solo_zero_final`,
  `Arith.Final0.pass_stays`, `Arith.sum_solo_pass`).  That gives the
  normal form of two additions with its two numerals
  (`Arith.two_sums_normal`), and with it, for all arguments: a run that
  ends at rest has made `(m + 1) + (m' + 1)` claims and has both
  numerals in memory (`Arith.two_sums_rest`), a fair run comes to rest
  (`Arith.two_sums_fair_all`), and the count of the agents at rest
  holds too (`Arith.two_sums_memOk_all`, `Arith.two_sums_census`).
  The numerals and the count together say that nothing else is in
  memory.  The agents of a numeral, from its head down, are a list fixed
  by the head, because an agent has one symbol and a wire one other end
  (`Arith.NumList`, `Arith.NumList.det`); so no agent is in it twice
  (`Arith.NumList.nodup`), and the numeral `k` has `k + 1` agents
  (`Arith.Num.list`).  A wire stays in one net, since every segment
  does, so the agents of the numeral on a free port are in the net of
  that port (`Arith.paired_tag`, `Arith.NumList.tag`), and the two
  numerals share no agent.  They have `(m + n + 1) + (m' + n' + 1)`
  agents between them, all in memory, and the memory holds that many
  agents; a list without repeats inside a list that is no longer holds
  every member of it (`Arith.nodup_cover`).  So at rest every agent in
  memory is an agent of one of the two numerals
  (`Arith.numerals_cover`, `Arith.two_sums_exact`).  This is about the
  agents.  The memory also keeps every segment that was ever written,
  on a wire between two ends or not; the segments are not counted
  here.  Two is not special.  Any number of nets side by side, each
  under its own tag, are a well-formed net when each is
  (`Arith.besides`, `Arith.besides_wf`).  A memory that holds a list of
  nets, cells in the order of the list, lets one thread do on the first
  net what it does on that net alone; when it has finished it is idle,
  and the same memory with those cells listed last holds the other nets
  and what the run left (`Arith.Holds`, `Arith.Holds.run`).  Doing this
  for each net in turn brings every net to what one thread leaves of it
  (`Arith.phases`); a last pass over them all only reads
  (`Arith.pass_all`), so the memory is a normal form, reached in as many
  steps as the runs have claims (`Arith.besides_normal`).  For a list of
  additions this gives the normal form with every sum on its free port
  (`Arith.sums_normal`), and so, with any number of threads and any
  schedule, a run that ends at rest has made `m + 1` claims for each
  addition `m + n` and has the numeral `m + n` of the `j`-th addition
  on the free port `([0, j], 0)`; and a fair run comes to rest
  (`Arith.sums_rest`, `Arith.sums_fair`).  The count of the agents at
  rest, and that nothing else is in memory, hold for any number of
  additions as well.  A list of additions side by side is a memory in
  order (`Arith.sums_memOk`), so the counts of the two-addition case
  apply as they stand: at rest no cell of a first argument and no adder
  is left, and the memory holds the successors of every sum and one zero
  for each addition (`Arith.sums_rest_first`, `Arith.sums_rest_adders`,
  `Arith.sums_census`).  In the memory that the nets reduce to, a
  segment that starts in the net of one addition ends in it
  (`Arith.Holds.link_tag`, `Arith.sums_normal_tags`), so the agents of
  the numeral on a free port are in the net of that port, and the
  numerals of different additions share no agent, a name having one tag
  (`Arith.NumList.tagc`, `Arith.tagged_unique`).  Their agents, all
  together, are as many as the memory holds (`Arith.numerals_all`), so
  every agent in memory is an agent of the numeral of one of the
  additions (`Arith.sums_exact`).
  The side-by-side results above are proved from the run of one thread
  on each net.  They also follow from reduction alone, and then for any
  nets.  A net made of nets under different tags (`Net.Made`) takes a
  step whenever a part does, and is then made of the same parts with
  that one replaced (`Net.Made.step`); it is normal when its parts are
  (`Net.Made.normal`).  So when the parts have normal forms the whole
  reduces, in as many steps as the parts together, to the net made of
  the normal forms (`Net.Made.reduce`), and since a well-formed net has
  one normal form, the thread machine at rest holds exactly that net,
  with any number of threads and any schedule (`XMach.made_rest`,
  `XMach.made_fair`; for the addition system `Arith.besides_rest`,
  `Arith.besides_fair`, and for the numerals of the normal forms
  `Arith.besides_rest_num`).  This asks the rules to give every new
  agent to one of the two agents that meet (`System.Sided`; true of
  addition, `Arith.system_sided`).  An agent that belongs to neither is
  named after one of the two by comparing their names, and a tag at the
  end of both names can change the comparison; with such agents the
  whole reaches the normal forms up to a renaming only, which is proved
  for two nets (`XMach.tagged_rest`, below).  The nets are side by side: no wire runs from one to
  another.  Wires between nets are made by plugging: new segments join
  free ports, which stop being free and become points of longer wires
  (`Net.plug`).  A step of a net is a step of the plugged net, whatever
  the system and the new segments (`Step.plug`, `Steps.plug`): the wire
  of an active pair runs through no end, and plugging makes no new
  ends.  The plugged net is well formed when the new segments are a
  finite matching of free ports (`Net.WF.plug`), and two wires that
  ended at joined ports are then one wire (`Net.Conn.plug`).  What a
  plugged net reduces to once its parts have met is not said by this:
  new active pairs can form across the new segments.  For addition it
  is worked out in one case, the result of one adder wired to the first
  argument of another.  The first net reduces inside the whole as it
  does alone; its sum is then, across the new segment, the first
  argument of the second adder, so the whole is a net that addition is
  about and `Arith.add_correct` applies again (`Arith.add_add`).  The
  nets `Arith.sum3 m n k` are built this way from the net for `m + n`
  and an adder that waits for its first argument (`Arith.openSnd`,
  `Arith.OpenAdd`), and they come out right for all `m`, `n`, `k`:
  `(m + 1) + (m + n + 1)` claims and the numeral `m + n + k`, with any
  number of threads and any schedule (`Arith.sum3_rest`,
  `Arith.sum3_fair`).  The same works with both arguments computed: an
  adder that waits for both (`Arith.Open2`) is wired to two nets that
  each compute a number on a free port (`Arith.Evals`), and the whole
  computes the sum on the free port of the adder (`Arith.add_evals`).
  The conclusion has the shape of the hypotheses, so it gives every
  expression built from numerals and additions (`Arith.Expr`): its net
  (`Arith.Expr.net`) is well formed and computes its value, in one more
  interaction per addition than the value of the first argument
  (`Arith.Expr.good`).  So with any number of threads and any schedule
  a run that ends at rest has made that many claims and has the numeral
  of the value on the free port, and a fair run comes to rest
  (`Arith.Expr.rest`, `Arith.Expr.fair`).  The count tells the two ways
  of bracketing apart: `(e₁ + e₂) + e₃` costs the value of `e₁` more
  than `e₁ + (e₂ + e₃)`, which on the machine is exactly that many more
  claims, whatever the threads and the schedules
  (`Arith.Expr.cost_assoc`, `Arith.Expr.assoc_rest`); and of the two
  orders of an addition the one with the smaller term first is cheaper
  (`Arith.Expr.cost_comm`).  The nets of expressions are
  not compact, a wire between two nets having three segments; that they
  are well formed comes from `Net.Made.wf` and `Net.WF.plug`, not from
  the validator, and the results about the list reducers, which ask for
  compact nets, do not apply to them.  Only the claims are counted;
  nothing is said about how many actions the threads take.  An
  expression can be run (`Arith.Expr.run`): a number of threads take
  turns on its net for a number of actions, and if they are then at
  rest the numeral on the free port is read by `XNet.readNum`, which
  follows wires of several segments as a thread does.  What `readNum`
  returns is a numeral of the net (`XNet.readNum_sound`), and a port
  carries at most one (`Addition.IsNum.unique`), so whatever the run
  returns is the value of the expression (`Arith.Expr.run_sound`).
  Given enough actions the run does return it
  (`Arith.Expr.run_complete`): threads that take turns are scheduled
  fairly, so they come to rest; from then on the memory does not change
  (`XMach.trace_rest_eq`), and `readNum` returns every numeral of a
  well-formed memory given enough fuel (`XNet.readNum_complete`).  How
  many actions are enough is not bounded; two runs are evaluated in the
  kernel.  The reader and the run are for any system with a zero and a
  successor (`XNet.runRead`): when the net of a memory reduces to a
  normal form with the numeral `v` on a port, whatever the run returns
  for that port is `v` (`XNet.runRead_sound`), and with enough actions
  it returns `v` (`XNet.runRead_complete`).
  Tags are one way to keep the names of nets apart, and they are what
  asks for rules with sides.  Without them, two nets can be put side by
  side as they are (`Net.union`) when no name of one, with any numbers
  in front, is a name of the other with any numbers in front
  (`Net.Apart`): new agents are named by putting a number in front of
  the name of an agent that fires, so names that are apart stay apart
  (`Net.Apart.fire`).  Then, in any system, a reduction of a
  well-formed net is a reduction of the net beside another and with any
  ports of the two joined (`Steps.context`); the union of well-formed
  nets is well formed and the union of normal nets is normal
  (`Net.WF.union`, `Net.Apart.normal`); so two nets with normal forms
  side by side reduce to the two normal forms side by side
  (`Net.Apart.reduce`), and the thread machine at rest holds exactly
  those (`XMach.union_rest`, `XMach.union_fair`).  The same holds for
  any number of nets, the names of any two of them apart
  (`Net.unions_reduce`, `XMach.unions_rest`).  A part can also be
  reduced first: if a net reduces to `A'`, and the larger net with `A'`
  in its place reduces to a normal form, the larger net reduces to that
  normal form in the steps of both (`Steps.part_first`), so that is
  what the thread machine reaches, and the claims it makes
  (`XMach.part_first`).  Names that end in different tags are apart
  (`Net.Apart.of_tags`).  Putting a tag at the end of every name is a
  renaming (`Renaming.tag`), and a reduction of a net is a reduction of
  the renamed net up to a renaming of what it reaches (`Steps.map`).
  So two memories put side by side under different tags come out right
  in any system, rules with sides or not: at rest the claims are the
  steps of the two reductions, and the memory holds the two normal
  forms side by side, each renamed, the names of the start carrying
  the tag (`XMach.tagged_rest`).  It is used in `UnionExamples` on the
  system `Solo`, whose rule makes an agent of neither side: what
  `normalize` returns is reached by steps (`XNet.normalize_steps`), and
  two copies of the net `aa` side by side under tags make two claims and
  leave two renamed normal forms, with any number of threads and any
  schedule.  For one
  addition, the condition on the number of threads in
  `Arith.threads_exact` is a limit of the proof: the thread
  numbered `t` has the `t` top successors last in its list, and must come
  to each after the round that takes it.  The agents the first thread has
  not taken are in memory after each of its actions
  (`Arith.solo_alive`), so the thread makes three actions on each
  successor of its chain and on each agent of the second argument, and
  that count gives the second condition; the first asks for four
  successors in the chain of every thread.  For two threads the
  conditions are `m` from four on, for three from six on; in the runs
  computed the other threads never claim at smaller sizes either.
  Nothing is proved for more threads than that, or for schedules that
  leave round robin earlier.  The alternating run is followed while successors are left on
  the first argument only, so the count is a lower bound on the work of
  the whole run, not its work.
* The proof that the adder adds is not about the system `Arith`.  It is
  given in `Addition` for any system with three different symbols and
  the two rules of unary addition among its rules (`Addition.Rules`);
  numerals, towers and the situation that addition is about are defined
  there from the arities and the three symbols, and the adder runs for
  `m + 1` steps and leaves the numeral `m + n` and no adder
  (`Addition.Config.steps`).  That what is left is a normal form needs
  more: it holds when every rule of the system involves an adder
  (`Addition.add_correct`), as in `Arith`.  The notions of `Arith` are
  those of `Addition` at its symbols (`Arith.rules`).  What is proved
  after that in `Arith` is still stated for `Arith`: the nets `sum m n`,
  the runs of the threads on them, side by side, one addition after
  another and expressions.  It reaches a larger system in another way.
  A map of symbols that keeps the arities and the rules puts one system
  inside another (`System.Embeds`); a net of the smaller system with its
  symbols relabelled then reduces in the larger one step for step
  (`Steps.relabel`), is well formed and is normal when the net is
  (`Net.WF.relabel`, `Net.relabel_normal`), so the thread machine of the
  larger system reaches on the relabelled memory what the net reduces
  to, with the same claims (`XMach.relabel_rest`, `XMach.relabel_fair`),
  and with the same numerals (`Arith.carry_rest`).  This covers nets
  whose agents all come from the smaller system; a net that also has
  other agents is the business of `Addition`.  The system `Peano` has
  both: seven more symbols, for multiplying, copying, erasing, powers,
  factorials, the lazy caterer and the triangular numbers, and the rules
  for them.  It contains addition (`Peano.rules`,
  `Peano.add_steps`) and has `Arith` inside it (`Peano.embeds`), so
  every expression of additions comes out right in it
  (`Peano.expr_rest`).  The two helpers of multiplication are proved, in
  a net that may have any other agents.  An eraser facing a numeral `n`
  runs for `n + 1` steps, after which it and the agents of the numeral
  are gone and nothing new is there (`Peano.erase`); a copier facing a
  numeral `n` runs for `n + 1` steps, after which the two ports its
  copies were wired to, free or not, carry the numeral `n`
  (`Peano.copy`).  Both say what the run leaves alone: `N.Keeps ar C N'`
  holds when the agents of `N` with names outside `C`, and the pairs of
  ends of `N` on names outside `C`, are in `N'`; one firing keeps
  everything away from its two agents (`Site.keeps`).  Here `C` is the
  eraser or copier, the agents of the numeral and the names not in use
  (`Addition.gone`).  That set is closed, the principal port of each of
  its names being wired to one of its names (`Addition.gone_closed`),
  and a numeral held at a port outside a closed set lies outside it, so
  it is kept (`Addition.IsNum.keeps`).  The adder is proved in the same
  setting: with any other agents in the net, other adders among them,
  and its result wired to any port, it runs for as many steps as its
  first argument has agents and leaves the sum on that port
  (`Addition.Adding.run`).  The results of these runs are numerals given
  with the list of their agents and a predicate that the agents satisfy
  (`Addition.IsNumQ`); it is used to say that the agents are new, their
  names not having been in use at the start (`Peano.copy_fresh`).  A
  later run consumes such a numeral, and that its agents are new is what
  shows that the later run leaves the rest of the first net alone.
* The multiplier multiplies (`Peano.mul_correct`): a net whose multiplier
  has the numerals `m` and `n` as arguments and a free port as result
  (`Peano.Product`) reduces to a normal form with the numeral `m * n` on
  that port, in exactly `(m + 1) * (n + 2) + m * (n + 1)` steps.  This
  is a case of a theorem about a multiplier in any net
  (`Peano.Multiplying.run`): the net may have any other agents and the
  result may be wired to any port that is not on the multiplier or its
  arguments; the port then carries the numeral `m * n`, made of new
  agents, everything away from the multiplier and its two arguments is
  kept (`Net.Keeps` for `Addition.gone2`, a closed set), and the agents
  of the net are zeros, successors, or agents of the start other than
  the multiplier.  The proof is by recursion on the first argument.  On
  a zero, the multiplier puts a zero on its result and erases its
  second argument.  On a successor it leaves an adder and a new
  multiplier behind and copies its second argument, one copy for each;
  the new multiplier computes the product of the rest on the second
  argument of the adder, by the theorem itself, and the adder then adds
  its copy.  The nets
  `Peano.prod m n`, built by putting successors on the arguments of the
  multiplier of `0 * 0`, are valid and are such multiplications for all
  `m` and `n` (`Peano.good_prod`), so the theorems about the machine
  apply: a run on `prod m n` that is at rest, with any number of
  threads and any schedule, has made exactly that many interactions and
  holds the numeral `m * n` on the free port (`Peano.prod_rest`), and a
  fair run comes to rest (`Peano.prod_fair`).  The net of `mul_correct`
  has only the multiplier and its two arguments.
* Powers (`Peano.pow_correct`).  The system has an agent `pow` whose
  rules use the multiplier as the rules of the multiplier use the
  adder: `y ^ 0 = 1`, with `y` erased, and `y ^ S x = y * y ^ x`, with
  `y` copied.  In any net, with any other agents and its result wired
  to any port not on it or on its arguments, the agent with the
  numerals `e` and `b` as exponent and base reduces in `powCost e b`
  steps to a net in which that port carries the numeral `b ^ e`, made
  of new agents, and everything away from the agent and its arguments
  is kept (`Peano.Powering.run`).  The proof is by recursion on the
  exponent and uses the theorem for itself, for the power of the rest,
  and `Peano.Multiplying.run` for the multiplication, in a net that has
  other agents and with the result where the power needs it; this is
  what the statements about what a run leaves alone, and about results
  being made of new agents, are for.  For the nets `Peano.power e b`
  the theorems about the machine apply: a run at rest has made exactly
  `powCost e b` interactions and holds the numeral `b ^ e`
  (`Peano.power_rest`), and a fair run comes to rest
  (`Peano.power_fair`).  The count is given by a recursion, not in
  closed form: `powCost 0 b = b + 2`, and `powCost (e + 1) b` is
  `b + 2`, `powCost e b` and `prodCost b (b ^ e)` together.
* What the theorems for the multiplier and the power say is stated once
  (`Peano.Computes2`): in any net, an agent with the symbol whose two
  arguments are the numerals `m` and `n`, with its result wired to any
  port not on it or on its arguments, reduces in `c m n` steps to a net
  in which that port carries the numeral `f m n`, made of new agents,
  with everything away from the agent and its arguments kept and no new
  agents but zeros and successors.  `Peano.mul_computes` and
  `Peano.pow_computes` are the two theorems in this form, and
  `Peano.Computes1` is the form for one argument.  The factorial is the
  test of it.  The agent `fac` has the rules `0! = 1` and
  `(S x)! = x! * S x`, the second with a copier, a new successor, a
  multiplier and a new `fac`.  It computes the factorial
  (`Peano.fac_computes`): the proof is by recursion on the argument,
  uses itself for the factorial of the rest, with its result on the
  first argument of the multiplier, and then uses the multiplier only
  through `Peano.mul_computes`, on that result and on the new successor
  with its copy.  For the nets `Peano.facNet n` the result is a normal
  form (`Peano.fac_correct`) and the theorems about the machine apply
  (`Peano.fac_rest`, `Peano.fac_fair`); `3!` takes 52 interactions.  The
  adder is not of this form: its result contains the agents of its
  second argument, so it is not made of new agents only
  (`Addition.Adding.run` says what it is made of).  The expressions of
  the next item do not have factorials.
* The three proofs follow one course, and it is proved once, in two
  shapes (`PeanoRec`).  On a parameter, `f (S x) y = g y (f x y)`: the
  agent copies its second argument for a new agent of its own symbol and
  a combiner `g` (`Peano.iterSucc`, `Peano.iter_computes`); the
  multiplier and the power have this rule.  On the predecessor,
  `f (S x) = g (f x) (S x)`: the agent copies the rest of its argument,
  one copy for a new agent and the other under a new successor for the
  combiner (`Peano.primSucc`, `Peano.prim_computes`); the factorial has
  this rule.  The rule on a successor is a template in the two symbols;
  what the agent does on a zero is a hypothesis (`Peano.Zero2`,
  `Peano.Zero1`), met by the zero rules of the three agents for any
  agent that has them.  The combiner need only combine
  (`Peano.Combines2`): its result may reuse the agents of its second
  argument, so the adder is one (`Peano.add_combines`), and so is every
  agent that computes.  `Peano.mul_computes'`, `Peano.pow_computes'` and
  `Peano.fac_computes'` derive the three theorems again from these two,
  with the costs `prodCost`, `powCost` and `facCost`; the power and the
  factorial are derived with the derived multiplier.  The test is a new
  agent, the lazy caterer `cater`, added to the system with two rules:
  the rule of the factorial on a zero and `c (S x) = c x + S x`
  (`Peano.caterSucc`), which is the template on the predecessor with the
  adder.  It computes `c n = n (n + 1) / 2 + 1` (`Peano.cater_computes`,
  `Peano.two_mul_cate`) by the theorem on recursion alone, and the
  reducer stops on `c 3` with `7` after `caterCost 3 = 20` steps.
* The theorems for the machine are proved once for every agent that
  computes (`PeanoRun`).  For an agent of one argument, on the net
  `Peano.unaryNet op n`, and of two, on `Peano.binaryNet op m n`: with
  any number of threads and any schedule, a run at rest has made exactly
  `c n` (or `c m n`) interactions and holds the numeral of the value
  (`Peano.unary_rest`, `Peano.binary_rest`), and a fair run comes to rest
  (`Peano.unary_fair`, `Peano.binary_fair`).  The multiplier, the power,
  the factorial and the lazy caterer are cases (`Peano.prod_rest'`,
  `Peano.power_rest'`, `Peano.fac_rest'`, `Peano.cater_rest`, and the
  fair versions), through the theorems derived from recursion, so for
  them the chain from the rules to the machine goes through the general
  theorems alone.  The adder is not a case of these: its result is not
  made of new agents only.  It is a case of the next item.
* Expressions over any operators that compute (`PeanoGExpr`).  An
  operator is data (`Peano.Op1`, `Peano.Op2`): a symbol, its function,
  its cost and the proof that alone with numerals it reduces in that
  cost to the numeral of the value.  Every agent that computes gives one
  (`Peano.Op1.ofComputes`, `Peano.Op2.ofComputes`), and so does the adder
  (`Peano.addOp`).  Expressions (`Peano.GExpr`) are numerals and
  operators of one or two arguments applied to expressions; an operator
  of one argument waits on its argument as one of two does
  (`Peano.op_setup1`).  Every expression has a net that is well formed
  and computes its value in exactly `GExpr.cost` interactions
  (`GExpr.good`), on the machine under any schedule (`GExpr.rest`) and
  under fair ones (`GExpr.fair`), and it can be run and read
  (`GExpr.run_sound`, `GExpr.run_complete`).  The expressions of `+`, `*`
  and `^` are a case, with the same nets, values and costs
  (`PExpr.toG`, `PExpr.rest'`).  `c 2 + 2!` is run by two threads in the
  kernel and gives `6` in its 41 interactions.  A single operator on the
  machine (`Peano.Op2.rest`, `Peano.Op1.rest`, and the fair versions)
  brings in the adder (`Peano.sum_rest`, `Peano.sum_fair`).
* Any constant on a zero (`PeanoConst`).  Any rule that puts the numeral
  `k` on the result, and for two arguments erases the second, meets the
  hypothesis on a zero of the theorems on recursion
  (`Peano.zero1_const`, `Peano.zero2_const`), given checks bounded by `k`
  that are evaluated for the rule (`Peano.ConstRule`, `Peano.EraRule`).
  The zero rules of the factorial, the multiplier and the power are
  cases.  The test is a new agent, the triangular numbers `tri`, whose
  rule on a zero puts down `0`: `Peano.tri_computes` is the theorems on
  recursion and on constants applied to its rules, `Peano.tri_rest` and
  `Peano.tri_fair` are the theorems for operators, and `t (2 + 1) * 3!`
  is an expression.
* Expressions built from numerals with `+`, `*` and `^` (`Peano.PExpr`)
  have nets (`PExpr.net`): the nets of the two arguments and an adder, a
  multiplier or a power that waits, side by side under the tags `0`,
  `1` and `2`
  (`XNet.three`), with the result port of each argument wired to a port
  of the operator.  The rules of `Peano` give every new agent a side
  (`Peano.system_sided`), so the argument nets reduce inside the whole
  as they do alone (`Net.Made.steps`); the operator then has two
  numerals as arguments in a net of successors and zeros
  (`Peano.op_setup`), which is the situation of `Peano.add_steps'`,
  `Peano.mul_steps` and `Peano.pow_steps`.  Hence every such net is well formed and computes
  the value of its expression in exactly `PExpr.cost` interactions
  (`PExpr.good`), and on the machine, with any number of threads and any
  schedule, a run at rest has made that many interactions and holds the
  numeral of the value on its free port (`PExpr.rest`); a fair run comes
  to rest (`PExpr.fair`).  The cost counts `e₁ + 1` for an addition,
  `prodCost e₁ e₂` for a multiplication and `powCost e b` for a power,
  on the values of the arguments.
  The proof evaluates the operators on numerals, which is one order of
  reduction; the count is the same for every order because the system
  is confluent.  These expressions can be run too (`PExpr.run`):
  whatever the run returns is the value (`PExpr.run_sound`), and with
  enough actions it returns the value (`PExpr.run_complete`); three
  runs are evaluated in the kernel, one of them `2 ^ (1 + 1)`.  How many actions are enough is not
  bounded.
* An executable system (`XSys`) carries proofs: that its rules are the rules
  of a `System`, and that the slots of each right-hand side are listed.  For
  a system given as data (`SysData`) these follow from the evaluation of
  `SysData.check`.  A right-hand side that lists an agent or a port twice,
  with different contents, is rejected even if the entries that lookups
  find describe a rule.
* Not in this development: multi-threaded code that runs, proved against `Mach`;
  weak memory; a work list of active pairs for the program with threads.

## Checking

No dependencies beyond the `Std` library that ships with Lean.  Checked with
Lean 4.35.0 by `lake build`.
The evaluated runs and checks (`Comb.xgg_run`, `Comb.xgd_normalize`,
`Comb.xloop_normalize`, `Comb.xloop_runLoops`, `Solo.xaa_normalize`,
`Comb.dsystem`, the parallel round on `Comb.xgg2`, the run on a renamed
`Comb.xgd`, and the first examples in `Arith`) are proved by `decide`, that
is, by evaluating the reducer and the validators inside the kernel.
The runs of the program (`Comb.xgg2_exec` and the examples after
`Arith.sum_exec`) are longer and use `decide +kernel`, which leaves the
whole evaluation to the kernel; it adds no axiom.
The theorems depend only on Lean's three standard axioms `propext`,
`Quot.sound` and `Classical.choice`; `Step.diamond` does not use the last.
-/
