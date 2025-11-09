#![cfg(feature = "alloc")]

use alloc::vec::Vec;
use core::hash::{Hash, Hasher};

const INITIAL_CAPACITY: usize = 16;
const LOAD_FACTOR_NUM: usize = 7; // 0.7
const LOAD_FACTOR_DEN: usize = 10;

#[derive(Debug)]
enum Bucket<K, V> {
    Empty,
    Tombstone,
    Occupied(K, V),
}

/// A very small HashMap implementation using open addressing (linear probing).
/// Not intended to be a full replacement of `std::collections::HashMap`, but
/// provides `new`, `insert`, `get`, `remove`, `len`, and `is_empty`.
pub struct HashMap<K, V> {
    buckets: Vec<Bucket<K, V>>,
    len: usize,
}

impl<K, V> HashMap<K, V> {
    /// Create a new empty HashMap.
    pub fn new() -> Self {
        let mut buckets = Vec::with_capacity(INITIAL_CAPACITY);
        buckets.resize_with(INITIAL_CAPACITY, || Bucket::Empty);
        Self { buckets, len: 0 }
    }

    fn capacity(&self) -> usize {
        self.buckets.len()
    }

    fn should_grow(&self) -> bool {
        self.len * LOAD_FACTOR_DEN >= self.capacity() * LOAD_FACTOR_NUM
    }

    fn make_hash<Q: ?Sized + Hash>(key: &Q) -> u64
    where
        K: core::borrow::Borrow<Q>,
    {
        // Simple FNV-1a 64-bit hasher
        struct FnvHasher(u64);
        impl Hasher for FnvHasher {
            fn write(&mut self, bytes: &[u8]) {
                const FNV_OFFSET: u64 = 0xcbf29ce484222325;
                const FNV_PRIME: u64 = 0x00000100000001B3;
                let mut h = if self.0 == 0 { FNV_OFFSET } else { self.0 };
                for &b in bytes {
                    h ^= b as u64;
                    h = h.wrapping_mul(FNV_PRIME);
                }
                self.0 = h;
            }
            fn finish(&self) -> u64 {
                if self.0 == 0 {
                    0xcbf29ce484222325
                } else {
                    self.0
                }
            }
        }

        let mut h = FnvHasher(0);
        key.hash(&mut h);
        h.finish()
    }

    fn probe_index(&self, hash: u64, i: usize) -> usize {
        // linear probing
        ((hash as usize) + i) & (self.capacity() - 1)
    }

    fn resize(&mut self, new_cap: usize)
    where
        K: Clone + Hash,
        V: Clone,
    {
        let mut new = Vec::with_capacity(new_cap);
        new.resize_with(new_cap, || Bucket::Empty);

        for bucket in core::mem::replace(&mut self.buckets, new).into_iter() {
            if let Bucket::Occupied(k, v) = bucket {
                self.insert_internal(k, v);
            }
        }
    }

    fn insert_internal(&mut self, key: K, value: V)
    where
        K: Hash,
    {
        let hash = Self::make_hash(&key);
        let mut first_tombstone: Option<usize> = None;
        for i in 0..self.capacity() {
            let idx = self.probe_index(hash, i);
            match &mut self.buckets[idx] {
                Bucket::Empty => {
                    let insert_idx = first_tombstone.unwrap_or(idx);
                    self.buckets[insert_idx] = Bucket::Occupied(key, value);
                    self.len += 1;
                    return;
                }
                Bucket::Tombstone => {
                    if first_tombstone.is_none() {
                        first_tombstone = Some(idx);
                    }
                }
                Bucket::Occupied(_k, _v) => {
                    // nothing to do here for insert_internal
                }
            }
        }
    }

    /// Insert a key-value pair. If the key already exists, replace the value and return the old value.
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Eq + Hash,
    {
        if self.should_grow() {
            let new_cap = self.capacity() * 2;
            // rehash into bigger table by taking ownership
            let old = core::mem::replace(&mut self.buckets, Vec::new());
            let mut new = Vec::with_capacity(new_cap);
            new.resize_with(new_cap, || Bucket::Empty);
            self.buckets = new;
            self.len = 0;
            for bucket in old.into_iter() {
                if let Bucket::Occupied(k, v) = bucket {
                    self.insert(k, v);
                }
            }
        }

        let hash = Self::make_hash(&key);
        let mut first_tombstone: Option<usize> = None;
        for i in 0..self.capacity() {
            let idx = self.probe_index(hash, i);
            match &mut self.buckets[idx] {
                Bucket::Empty => {
                    let insert_idx = first_tombstone.unwrap_or(idx);
                    self.buckets[insert_idx] = Bucket::Occupied(key, value);
                    self.len += 1;
                    return None;
                }
                Bucket::Tombstone => {
                    if first_tombstone.is_none() {
                        first_tombstone = Some(idx);
                    }
                }
                Bucket::Occupied(k, v) => {
                    if k == &key {
                        // replace
                        let old = core::mem::replace(v, value);
                        return Some(old);
                    }
                }
            }
        }

        // Table full (shouldn't happen due to grow), put in first tombstone if any
        if let Some(idx) = first_tombstone {
            self.buckets[idx] = Bucket::Occupied(key, value);
            self.len += 1;
            return None;
        }

        None
    }

    /// Get a reference to a value by key.
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: core::borrow::Borrow<Q> + Hash + Eq,
        Q: Hash + Eq,
    {
        if self.capacity() == 0 {
            return None;
        }
        let hash = Self::make_hash(key);
        for i in 0..self.capacity() {
            let idx = self.probe_index(hash, i);
            match &self.buckets[idx] {
                Bucket::Empty => return None,
                Bucket::Tombstone => continue,
                Bucket::Occupied(k, v) => {
                    if k.borrow() == key {
                        return Some(v);
                    }
                }
            }
        }
        None
    }

    /// Remove a key from the map, returning the value if existed.
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: core::borrow::Borrow<Q> + Hash + Eq,
        Q: Hash + Eq,
    {
        if self.capacity() == 0 {
            return None;
        }
        let hash = Self::make_hash(key);
        for i in 0..self.capacity() {
            let idx = self.probe_index(hash, i);
            match core::mem::replace(&mut self.buckets[idx], Bucket::Empty) {
                Bucket::Empty => {
                    // restore
                    self.buckets[idx] = Bucket::Empty;
                    return None;
                }
                Bucket::Tombstone => {
                    self.buckets[idx] = Bucket::Tombstone;
                    continue;
                }
                Bucket::Occupied(k, v) => {
                    if k.borrow() == key {
                        self.buckets[idx] = Bucket::Tombstone;
                        self.len -= 1;
                        return Some(v);
                    } else {
                        self.buckets[idx] = Bucket::Occupied(k, v);
                    }
                }
            }
        }
        None
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.buckets.iter().filter_map(|bucket| {
            if let Bucket::Occupied(k, v) = bucket {
                Some((k, v))
            } else {
                None
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::HashMap;

    #[test]
    fn basic_insert_get_remove() {
        let mut m = HashMap::new();
        assert!(m.is_empty());
        assert_eq!(m.insert(1u32, "one"), None);
        assert_eq!(m.len(), 1);
        assert_eq!(m.get(&1u32), Some(&"one"));
        assert_eq!(m.insert(1u32, "uno"), Some("one"));
        assert_eq!(m.get(&1u32), Some(&"uno"));
        assert_eq!(m.remove(&1u32), Some("uno"));
        assert!(m.is_empty());
    }
}
