use super::*;

use canbench_rs::{bench, bench_fn, BenchResult};
use tiny_rng::{Rand, Rng};

enum SetUpStrategy {
    // Every neuron follows a single neuron.
    Centralized {
        num_neurons: u64,
    },
    // Following is centralized, but the voter neuron isn't followed by any other neuron.
    SingleVote {
        num_neurons: u64,
    },
    // Neurons follow a chain of other neurons. One end of the chain votes triggering the chain all
    // the way to the other end, while every neuron has its allowed followees maximized. This is
    // close to the worst case scenario. TODO: an even worse case scenario would be that the
    // catch-all topic following are also maximized while contributing nothing to the voting. The
    // worse scenario can be improved by just changing the following index though.
    Chain {
        num_neurons: u64,
        num_followees: u64,
    },
}

fn set_up<NS: NeuronStore>(
    stratygy: SetUpStrategy,
    rng: &mut Rng,
    neuron_store: &mut NS,
    existing_votes: &mut HashMap<NeuronId, Vote>,
) -> NeuronId {
    match stratygy {
        SetUpStrategy::Centralized { num_neurons } => {
            set_up_centralized(num_neurons, rng, neuron_store, existing_votes)
        }
        SetUpStrategy::SingleVote { num_neurons } => {
            set_up_single_vote(num_neurons, rng, neuron_store, existing_votes)
        }

        SetUpStrategy::Chain {
            num_neurons,
            num_followees,
        } => set_up_chain(
            num_neurons,
            num_followees,
            rng,
            neuron_store,
            existing_votes,
        ),
    }
}

fn set_up_centralized<NS: NeuronStore>(
    num_neurons: u64,
    rng: &mut Rng,
    neuron_store: &mut NS,
    existing_votes: &mut HashMap<NeuronId, Vote>,
) -> NeuronId {
    assert!(num_neurons > 1);

    let start_neuron_id = NeuronId::from(rng.rand_u64());

    neuron_store.set_followees(start_neuron_id, Topic::from(1u8), vec![]);
    existing_votes.insert(start_neuron_id, Vote::Unspecified);

    for _ in 1u64..=num_neurons {
        let follower_neuron_id = rng.rand_u64();
        neuron_store.set_followees(
            FollowerNeuronId::from(follower_neuron_id),
            Topic::from(1u8),
            vec![start_neuron_id],
        );
        existing_votes.insert(NeuronId::from(follower_neuron_id), Vote::Unspecified);
    }

    start_neuron_id
}

fn set_up_single_vote<NS: NeuronStore>(
    num_neurons: u64,
    rng: &mut Rng,
    neuron_store: &mut NS,
    existing_votes: &mut HashMap<NeuronId, Vote>,
) -> NeuronId {
    assert!(num_neurons > 1);

    let start_neuron_id = NeuronId::from(rng.rand_u64());
    let central_neuron_id = NeuronId::from(rng.rand_u64());

    existing_votes.insert(start_neuron_id, Vote::Unspecified);
    existing_votes.insert(central_neuron_id, Vote::Unspecified);

    for _ in 2u64..=num_neurons {
        let neuron_id = rng.rand_u64();
        neuron_store.set_followees(
            FollowerNeuronId::from(neuron_id),
            Topic::from(1u8),
            vec![central_neuron_id],
        );
        existing_votes.insert(NeuronId::from(neuron_id), Vote::Unspecified);
    }

    start_neuron_id
}

fn set_up_chain<NS: NeuronStore>(
    num_neurons: u64,
    num_followees: u64,
    rng: &mut Rng,
    neuron_store: &mut NS,
    existing_votes: &mut HashMap<NeuronId, Vote>,
) -> NeuronId {
    assert!(num_followees % 2 == 1, "Number of followees must be odd");
    assert!(
        num_neurons > num_followees,
        "Number of neurons must be greater than number of followees"
    );

    let num_half_followees = num_followees / 2;

    let neuron_ids: Vec<NeuronId> = (0u64..num_neurons)
        .map(|_| NeuronId::from(rng.rand_u64()))
        .collect();

    let not_voting_neuron_ids = (0u64..num_half_followees)
        .map(|i| NeuronId::from(neuron_ids[i as usize]))
        .collect::<Vec<_>>();
    for not_voting_neuron_id in not_voting_neuron_ids.iter() {
        existing_votes.insert(*not_voting_neuron_id, Vote::Unspecified);
    }

    for voted_neuron_index in num_half_followees..(num_half_followees * 2) {
        existing_votes.insert(
            NeuronId::from(neuron_ids[voted_neuron_index as usize]),
            Vote::Yes,
        );
    }

    let start_neuron_id = NeuronId::from(neuron_ids[(num_half_followees * 2) as usize]);
    existing_votes.insert(start_neuron_id, Vote::Unspecified);

    for neuron_index in num_followees..num_neurons {
        let neuron_id = neuron_ids[neuron_index as usize];
        let previous_neuron_indices = (neuron_index - num_half_followees - 1)..neuron_index;
        let followee_neuron_ids = previous_neuron_indices
            .map(|index| NeuronId::from(neuron_ids[index as usize]))
            .chain(not_voting_neuron_ids.clone().into_iter())
            .collect::<Vec<_>>();
        neuron_store.set_followees(
            FollowerNeuronId::from(neuron_id),
            Topic::from(1u8),
            followee_neuron_ids,
        );
        existing_votes.insert(NeuronId::from(neuron_id), Vote::Unspecified);
    }

    start_neuron_id
}

fn bench_helper(neuron_store: &mut impl NeuronStore, stratygy: SetUpStrategy) -> BenchResult {
    let mut existing_votes = HashMap::new();
    let mut rng = Rng::from_seed(0u64);

    let neuron_id = set_up(stratygy, &mut rng, neuron_store, &mut existing_votes);

    bench_fn(|| {
        let cascaded_votes = calculate_cascaded_votes(
            existing_votes,
            neuron_id,
            Vote::Yes,
            Topic::from(1u8),
            neuron_store,
        );
        println!("Number of cascaded votes: {}", cascaded_votes.len());
    })
}

#[bench(raw)]
fn vote_cascading_stable_centralized_1k() -> BenchResult {
    let mut neuron_store = StableNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Centralized { num_neurons: 1_000 },
    )
}

#[bench(raw)]
fn vote_cascading_stable_centralized_10k() -> BenchResult {
    let mut neuron_store = StableNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Centralized {
            num_neurons: 10_000,
        },
    )
}

#[bench(raw)]
fn vote_cascading_stable_single_vote_1k() -> BenchResult {
    let mut neuron_store = StableNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::SingleVote { num_neurons: 1_000 },
    )
}

#[bench(raw)]
fn vote_cascading_stable_single_vote_10k() -> BenchResult {
    let mut neuron_store = StableNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::SingleVote {
            num_neurons: 10_000,
        },
    )
}

#[bench(raw)]
fn vote_cascading_stable_chain_1k_15() -> BenchResult {
    let mut neuron_store = StableNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Chain {
            num_neurons: 1_000,
            num_followees: 15,
        },
    )
}

#[bench(raw)]
fn vote_cascading_stable_chain_10k_15() -> BenchResult {
    let mut neuron_store = StableNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Chain {
            num_neurons: 10_000,
            num_followees: 15,
        },
    )
}

#[bench(raw)]
fn vote_cascading_stable_chain_1k_5() -> BenchResult {
    let mut neuron_store = StableNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Chain {
            num_neurons: 1_000,
            num_followees: 5,
        },
    )
}

#[bench(raw)]
fn vote_cascading_stable_chain_10k_5() -> BenchResult {
    let mut neuron_store = StableNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Chain {
            num_neurons: 10_000,
            num_followees: 5,
        },
    )
}

#[bench(raw)]
fn vote_cascading_heap_centralized_1k() -> BenchResult {
    let mut neuron_store = HeapNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Centralized { num_neurons: 1_000 },
    )
}

#[bench(raw)]
fn vote_cascading_heap_centralized_10k() -> BenchResult {
    let mut neuron_store = HeapNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Centralized {
            num_neurons: 10_000,
        },
    )
}

#[bench(raw)]
fn vote_cascading_heap_single_vote_1k() -> BenchResult {
    let mut neuron_store = HeapNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::SingleVote { num_neurons: 1_000 },
    )
}

#[bench(raw)]
fn vote_cascading_heap_single_vote_10k() -> BenchResult {
    let mut neuron_store = HeapNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::SingleVote {
            num_neurons: 10_000,
        },
    )
}

#[bench(raw)]
fn vote_cascading_heap_chain_1k_15() -> BenchResult {
    let mut neuron_store = HeapNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Chain {
            num_neurons: 1_000,
            num_followees: 15,
        },
    )
}

#[bench(raw)]
fn vote_cascading_heap_chain_10k_15() -> BenchResult {
    let mut neuron_store = HeapNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Chain {
            num_neurons: 10_000,
            num_followees: 15,
        },
    )
}

#[bench(raw)]
fn vote_cascading_heap_chain_1k_5() -> BenchResult {
    let mut neuron_store = HeapNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Chain {
            num_neurons: 1_000,
            num_followees: 5,
        },
    )
}

#[bench(raw)]
fn vote_cascading_heap_chain_10k_5() -> BenchResult {
    let mut neuron_store = HeapNeuronStore::new();
    bench_helper(
        &mut neuron_store,
        SetUpStrategy::Chain {
            num_neurons: 10_000,
            num_followees: 5,
        },
    )
}
