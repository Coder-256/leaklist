use leaklist::LeakList;

fn main() {
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
}
