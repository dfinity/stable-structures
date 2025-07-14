use super::*;

use maplit::hashmap;

fn combine_votes(
    existing_votes: HashMap<NeuronId, Vote>,
    new_votes: HashMap<NeuronId, Vote>,
) -> HashMap<NeuronId, Vote> {
    let mut combined_votes = existing_votes.clone();
    for (neuron_id, vote) in new_votes {
        combined_votes.insert(neuron_id, vote);
    }
    combined_votes
}

fn test_two_neurons_specific_topic(neuron_store: &mut impl NeuronStore) {
    let existing_votes = hashmap! {
        1 => Vote::Unspecified,
        2 => Vote::Unspecified,
    };
    neuron_store.set_followees(2, Topic::from(1u8), vec![1]);

    let cascaded_votes = calculate_cascaded_votes(
        existing_votes,
        NeuronId::from(1u64),
        Vote::Yes,
        Topic::from(1u8),
        neuron_store,
    );

    assert_eq!(
        cascaded_votes,
        hashmap! {
            1 => Vote::Yes,
            2 => Vote::Yes,
        }
    );
}

#[test]
fn test_two_neurons_specific_topic_stable() {
    let mut neuron_store = StableNeuronStore::new();
    test_two_neurons_specific_topic(&mut neuron_store);
}

#[test]
fn test_two_neurons_specific_topic_heap() {
    let mut neuron_store = HeapNeuronStore::new();
    test_two_neurons_specific_topic(&mut neuron_store);
}

fn test_two_neurons_catch_all_topic(neuron_store: &mut impl NeuronStore) {
    let existing_votes = hashmap! {
        1 => Vote::Unspecified,
        2 => Vote::Unspecified,
    };
    neuron_store.set_followees(2, Topic::from(0u8), vec![1]);

    let cascaded_votes = calculate_cascaded_votes(
        existing_votes,
        NeuronId::from(1u64),
        Vote::Yes,
        Topic::from(1u8),
        neuron_store,
    );

    assert_eq!(
        cascaded_votes,
        hashmap! {
            1 => Vote::Yes,
            2 => Vote::Yes,
        }
    );
}

#[test]
fn test_two_neurons_catch_all_topic_stable() {
    let mut neuron_store = StableNeuronStore::new();
    test_two_neurons_catch_all_topic(&mut neuron_store);
}

#[test]
fn test_two_neurons_catch_all_topic_heap() {
    let mut neuron_store = HeapNeuronStore::new();
    test_two_neurons_catch_all_topic(&mut neuron_store);
}

fn test_specific_override_catch_all(neuron_store: &mut impl NeuronStore) {
    let existing_votes = hashmap! {
        1 => Vote::Unspecified,
        2 => Vote::Unspecified,
        3 => Vote::Unspecified,
    };
    neuron_store.set_followees(3, Topic::from(0u8), vec![1]);
    neuron_store.set_followees(3, Topic::from(1u8), vec![2]);

    let cascaded_votes = calculate_cascaded_votes(
        existing_votes.clone(),
        NeuronId::from(1u64),
        Vote::Yes,
        Topic::from(1u8),
        neuron_store,
    );
    assert_eq!(
        cascaded_votes,
        hashmap! {
            1 => Vote::Yes,
        }
    );

    let existing_votes = combine_votes(existing_votes, cascaded_votes);
    let cascaded_votes = calculate_cascaded_votes(
        existing_votes,
        NeuronId::from(2u64),
        Vote::Yes,
        Topic::from(1u8),
        neuron_store,
    );
    assert_eq!(
        cascaded_votes,
        hashmap! {
            2 => Vote::Yes,
            3 => Vote::Yes,
        }
    );
}

#[test]
fn test_specific_override_catch_all_stable() {
    let mut neuron_store = StableNeuronStore::new();
    test_specific_override_catch_all(&mut neuron_store);
}

#[test]
fn test_specific_override_catch_all_heap() {
    let mut neuron_store = HeapNeuronStore::new();
    test_specific_override_catch_all(&mut neuron_store);
}

fn set_up_worst_case<NS: NeuronStore>(
    num_neurons: u64,
    num_followees: u64,
    neuron_store: &mut NS,
    existing_votes: &mut HashMap<NeuronId, Vote>,
) -> NeuronId {
    assert!(num_followees % 2 == 1, "Number of followees must be odd");
    assert!(
        num_neurons > num_followees,
        "Number of neurons must be greater than number of followees"
    );

    let num_half_followees = num_followees / 2;

    let not_voting_neuron_ids = (0u64..num_half_followees)
        .map(NeuronId::from)
        .collect::<Vec<_>>();
    for not_voting_neuron_id in not_voting_neuron_ids.iter() {
        existing_votes.insert(*not_voting_neuron_id, Vote::Unspecified);
    }

    for voted_neuron_id in num_half_followees..(num_half_followees * 2) {
        existing_votes.insert(NeuronId::from(voted_neuron_id), Vote::Yes);
    }

    let start_neuron_id = NeuronId::from(num_half_followees * 2);
    existing_votes.insert(start_neuron_id, Vote::Unspecified);

    for neuron_id in num_followees..num_neurons {
        let previous_neuron_ids = (neuron_id - num_half_followees - 1)..neuron_id;
        let followee_neuron_ids = previous_neuron_ids
            .map(|id| NeuronId::from(id))
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

fn test_chain(neuron_store: &mut impl NeuronStore) {
    let mut existing_votes = HashMap::new();
    let start_neuron_id = set_up_worst_case(100, 15, neuron_store, &mut existing_votes);

    let cascaded_votes = calculate_cascaded_votes(
        existing_votes,
        start_neuron_id,
        Vote::Yes,
        Topic::from(1u8),
        neuron_store,
    );

    assert_eq!(cascaded_votes.len(), 86);
}

#[test]
fn test_chain_stable() {
    let mut neuron_store = StableNeuronStore::new();
    test_chain(&mut neuron_store);
}

#[test]
fn test_chain_heap() {
    let mut neuron_store = HeapNeuronStore::new();
    test_chain(&mut neuron_store);
}
