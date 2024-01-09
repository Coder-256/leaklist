use leaklist::LeakList;

fn main() {
    let mut list: LeakList<u32> = LeakList::new();
    let node1 = list.push_front(1);
    let node2 = list.push_front(2);
    println!("node1: {:?}", node1);
    println!("node2: {:?}", node2);

    std::thread::scope(|s| {
        let list_ref = &list;
        for i in 3..=15 {
            s.spawn(move || list_ref.push_front(i));
        }
    });

    let removed = list.pop_front().expect("list is empty");
    assert!(removed > 2);
    println!("removed: {:?}", removed);

    println!("list: {:?}", list.iter().copied().collect::<Vec<u32>>());
    println!("moved list: {:?}", list.into_iter().collect::<Vec<u32>>());
}
