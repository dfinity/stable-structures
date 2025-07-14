use ic_stable_structures::{
    memory_manager::{MemoryId, MemoryManager, VirtualMemory},
    DefaultMemoryImpl, StableBTreeMap,
};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vote {
    Unspecified,
    Yes,
    No,
}

type NeuronId = u64;
type Topic = u8;

pub trait NeuronStore {
    fn set_followees(
        &mut self,
        follower_neuron_id: NeuronId,
        topic: Topic,
        followee_neuron_ids: Vec<NeuronId>,
    );
    fn get_followers(&self, followee_neuron_id: NeuronId, topic: Topic) -> Vec<NeuronId>;
    fn get_followees(&self, follower_neuron_id: NeuronId, topic: Topic) -> Vec<NeuronId>;
}

type VM = VirtualMemory<DefaultMemoryImpl>;

thread_local! {
    static MEMORY_MANAGER: RefCell<MemoryManager<DefaultMemoryImpl>> =
        RefCell::new(MemoryManager::init(DefaultMemoryImpl::default()));
}

type FolloweeNeuronId = NeuronId;
type FollowerNeuronId = NeuronId;
type FolloweeEntryTuple = (FollowerNeuronId, (Topic, u64));
type FollowerIndexTuple = ((Topic, FolloweeNeuronId), FollowerNeuronId);

struct StableNeuronStore {
    followees_map: StableBTreeMap<FolloweeEntryTuple, FolloweeNeuronId, VM>,
    followers_index: StableBTreeMap<FollowerIndexTuple, (), VM>,
}

const FOLLOWEES_MEMORY_ID: MemoryId = MemoryId::new(0);
const FOLLOWERS_MEMORY_ID: MemoryId = MemoryId::new(1);

impl StableNeuronStore {
    fn new() -> Self {
        MEMORY_MANAGER.with_borrow(|m| Self {
            followees_map: StableBTreeMap::new(m.get(FOLLOWEES_MEMORY_ID)),
            followers_index: StableBTreeMap::new(m.get(FOLLOWERS_MEMORY_ID)),
        })
    }
}

impl NeuronStore for StableNeuronStore {
    fn set_followees(
        &mut self,
        follower_neuron_id: FollowerNeuronId,
        topic: Topic,
        followee_neuron_ids: Vec<FolloweeNeuronId>,
    ) {
        let min_followee_map_key = (follower_neuron_id, (topic, u64::MIN));
        let max_followee_map_key = (follower_neuron_id, (topic, u64::MAX));
        let previous_followees = self
            .followees_map
            .range(min_followee_map_key..=max_followee_map_key)
            .map(|(_key, value)| value)
            .collect::<HashSet<_>>();
        let previous_followee_keys = self
            .followees_map
            .range(min_followee_map_key..=max_followee_map_key)
            .map(|(key, _value)| key)
            .collect::<Vec<_>>();
        for key in previous_followee_keys {
            self.followees_map.remove(&key);
        }
        let new_followees = followee_neuron_ids.iter().cloned().collect::<HashSet<_>>();
        for (index, followee_neuron_id) in followee_neuron_ids.into_iter().enumerate() {
            self.followees_map.insert(
                (follower_neuron_id, (topic, index as u64)),
                followee_neuron_id,
            );
        }
        let followees_to_remove = previous_followees.difference(&new_followees);
        for followee_neuron_id in followees_to_remove {
            let follower_index_key = ((topic, *followee_neuron_id), follower_neuron_id);
            self.followers_index.remove(&follower_index_key);
        }
        let followees_to_add = new_followees.difference(&previous_followees);
        for followee_neuron_id in followees_to_add {
            let follower_index_key = ((topic, *followee_neuron_id), follower_neuron_id);
            self.followers_index.insert(follower_index_key, ());
        }
    }

    fn get_followees(&self, follower_neuron_id: FolloweeNeuronId, topic: Topic) -> Vec<NeuronId> {
        let min_key = (follower_neuron_id, (topic, u64::MIN));
        let max_key = (follower_neuron_id, (topic, u64::MAX));

        self.followees_map
            .range(min_key..=max_key)
            .map(|(_key, followee_neuron_id)| followee_neuron_id)
            .collect()
    }

    fn get_followers(&self, followee_neuron_id: FolloweeNeuronId, topic: Topic) -> Vec<NeuronId> {
        let min_key = ((topic, followee_neuron_id), FollowerNeuronId::MIN);
        let max_key = ((topic, followee_neuron_id), FollowerNeuronId::MAX);

        self.followers_index
            .range(min_key..=max_key)
            .map(|(((_topic, _followee_neuron_id), follower_neuron_id), _value)| follower_neuron_id)
            .collect()
    }
}

struct HeapNeuronStore {
    followees: HashMap<FollowerNeuronId, HashMap<Topic, Vec<FolloweeNeuronId>>>,
    followers: BTreeMap<Topic, BTreeMap<FollowerNeuronId, BTreeSet<FollowerNeuronId>>>,
}

impl HeapNeuronStore {
    fn new() -> Self {
        Self {
            followees: HashMap::new(),
            followers: BTreeMap::new(),
        }
    }
}

impl NeuronStore for HeapNeuronStore {
    fn set_followees(
        &mut self,
        follower_neuron_id: FollowerNeuronId,
        topic: Topic,
        followee_neuron_ids: Vec<FolloweeNeuronId>,
    ) {
        let old_followees = self
            .followees
            .get(&follower_neuron_id)
            .and_then(|followees| followees.get(&topic).cloned())
            .unwrap_or_default()
            .into_iter()
            .collect::<BTreeSet<_>>();

        let followees = self.followees.entry(follower_neuron_id).or_default();
        if followee_neuron_ids.is_empty() {
            followees.remove(&topic);
        } else {
            followees.insert(topic, followee_neuron_ids.clone());
        }

        let new_followees = followee_neuron_ids.into_iter().collect::<BTreeSet<_>>();

        let followees_to_remove = old_followees.difference(&new_followees);
        for followee_neuron_id in followees_to_remove {
            let followers = self
                .followers
                .get_mut(&topic)
                .and_then(|followers| followers.get_mut(followee_neuron_id));
            if let Some(followers) = followers {
                followers.remove(&follower_neuron_id);
            }
        }

        let followees_to_add = new_followees.difference(&old_followees);
        for followee_neuron_id in followees_to_add {
            let followers = self
                .followers
                .entry(topic)
                .or_default()
                .entry(*followee_neuron_id)
                .or_default();
            followers.insert(follower_neuron_id);
        }
    }

    fn get_followees(&self, follower_neuron_id: FolloweeNeuronId, topic: Topic) -> Vec<NeuronId> {
        self.followees
            .get(&follower_neuron_id)
            .and_then(|followees| followees.get(&topic))
            .cloned()
            .unwrap_or_default()
    }

    fn get_followers(&self, followee_neuron_id: FolloweeNeuronId, topic: Topic) -> Vec<NeuronId> {
        self.followers
            .get(&topic)
            .and_then(|followers| followers.get(&followee_neuron_id))
            .map(|followers| followers.iter().copied().collect())
            .unwrap_or_default()
    }
}

fn would_follow<NS: NeuronStore>(
    neuron_id: NeuronId,
    topic: Topic,
    existing_votes: &HashMap<NeuronId, Vote>,
    new_votes: &HashMap<NeuronId, Vote>,
    neuron_store: &NS,
) -> Vote {
    let specific_followees = neuron_store.get_followees(neuron_id, topic);
    let followees = if specific_followees.is_empty() {
        neuron_store.get_followees(neuron_id, 0)
    } else {
        specific_followees
    };

    if followees.is_empty() {
        return Vote::Unspecified;
    }

    let mut yes = 0;
    let mut no = 0;

    for followee in &followees {
        let existing_vote = existing_votes.get(followee).copied();
        match existing_vote {
            Some(Vote::Yes) => yes += 1,
            Some(Vote::No) => no += 1,
            Some(Vote::Unspecified) | None => {
                let new_vote = new_votes.get(followee).copied();
                match new_vote {
                    Some(Vote::Yes) => yes += 1,
                    Some(Vote::No) => no += 1,
                    None => {}
                    Some(Vote::Unspecified) => {
                        unreachable!("New vote is unspecified");
                    }
                }
            }
        }

        if 2 * yes > followees.len() {
            return Vote::Yes;
        }
        if 2 * no >= followees.len() {
            return Vote::No;
        }
    }
    Vote::Unspecified
}

pub fn calculate_cascaded_votes<NS: NeuronStore>(
    existing_votes: HashMap<NeuronId, Vote>,
    voter_neuron_id: NeuronId,
    vote_of_neuron: Vote,
    topic: Topic,
    neuron_store: &NS,
) -> HashMap<NeuronId, Vote> {
    assert!(topic != 0);

    let mut induction_votes = HashMap::new();
    induction_votes.insert(voter_neuron_id, vote_of_neuron);

    let mut new_votes = HashMap::new();

    loop {
        let mut followers = BTreeSet::new();

        for (neuron_id, vote) in induction_votes.iter() {
            assert!(*vote != Vote::Unspecified);

            new_votes.insert(*neuron_id, *vote);

            followers.extend(neuron_store.get_followers(*neuron_id, topic));
            followers.extend(neuron_store.get_followers(*neuron_id, 0));
        }

        induction_votes.clear();

        followers.retain(|neuron_id| {
            let just_voted = new_votes.contains_key(neuron_id);
            let previous_vote = existing_votes.get(neuron_id).copied();
            !just_voted && previous_vote == Some(Vote::Unspecified)
        });

        for follower in followers {
            let induced_vote =
                would_follow(follower, topic, &existing_votes, &new_votes, neuron_store);
            if induced_vote != Vote::Unspecified {
                induction_votes.insert(follower, induced_vote);
            }
        }

        if induction_votes.is_empty() {
            return new_votes;
        }
    }
}

#[cfg(test)]
mod tests;

mod benches;
