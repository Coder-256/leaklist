# leaklist

[![GitHub](https://img.shields.io/badge/github-Coder--256%2Fleaklist-4c1.svg?logo=github)](https://github.com/Coder-256/leaklist)
[![License](https://img.shields.io/badge/license-MIT_OR_Apache--2.0-blue.svg)](https://github.com/Coder-256/leaklist#license)
[![docs.rs](https://docs.rs/leaklist/badge.svg)](https://docs.rs/leaklist/latest/leaklist/)

A leaky, concurrent, lock-free, singly-linked list. Only supports prepending
items, and will leak an allocation for each new element.

This type of list can be useful for setting up a chain of objects that only need
to be initialized once and will live for the duration of the program.

## Example

```rust
let list: LeakList<u32> = LeakList::new();
let node1 = list.push_front(1);
let node2 = list.push_front(2);
println!("node1: {:?}", node1);
println!("node2: {:?}", node2);

std::thread::scope(|s| {
    s.spawn(|| {
        let node3 = list.push_front(3);
        println!("node3: {:?}", node3);
    });
    s.spawn(|| {
        let node4 = list.push_front(4);
        println!("node4: {:?}", node4);
    });
});

println!("list: {:?}", list.iter().copied().collect::<Vec<_>>());
```

Output may be:

```
node1: Node { val: 1, next: None }
node2: Node { val: 2, next: Some(Node { val: 1, next: None }) }
node3: Node { val: 3, next: Some(Node { val: 2, next: Some(Node { val: 1, next: None }) }) }
node4: Node { val: 4, next: Some(Node { val: 3, next: Some(Node { val: 2, next: Some(Node { val: 1, next: None }) }) }) }
list: [4, 3, 2, 1]
```

Or:

```
node1: Node { val: 1, next: None }
node2: Node { val: 2, next: Some(Node { val: 1, next: None }) }
node4: Node { val: 4, next: Some(Node { val: 2, next: Some(Node { val: 1, next: None }) }) }
node3: Node { val: 3, next: Some(Node { val: 4, next: Some(Node { val: 2, next: Some(Node { val: 1, next: None }) }) }) }
list: [3, 4, 2, 1]
```

## License

This project is dual-licensed under the [MIT](LICENSE-MIT) and
[Apache-2.0](LICENSE-APACHE) licenses.
