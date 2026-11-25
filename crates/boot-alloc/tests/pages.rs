//! The heap gives each run back at its end: the process maps as many bytes
//! after the heap ends as before it started. The count reads the whole
//! process, so this target holds this one test alone.

#[cfg(test)]
mod host;

#[cfg(test)]
mod heap
{
    use core::alloc::Layout;

    use gandr_boot_alloc::Base;
    use gandr_boot_alloc::Bytes;
    use gandr_boot_alloc::Heap;

    use crate::host;

    /// The bytes that the process maps, from `/proc/self/statm`. The read
    /// fills a buffer on the stack, so it maps nothing itself.
    ///
    /// # Specification
    /// trivial.
    #[cfg(target_os = "linux")]
    fn mapped() -> Bytes
    {
        use std::io::Read as _;
        let mut file =
            std::fs::File::open("/proc/self/statm").expect("the kernel gives the process's statm");
        let mut buffer = [0_u8; 128];
        let read = file.read(&mut buffer).expect("the kernel writes statm");
        let text = core::str::from_utf8(&buffer[.. read]).expect("statm is text");
        let pages: usize = text
            .split(' ')
            .next()
            .and_then(|field| field.parse().ok())
            .expect("statm starts with a count");
        Bytes(
            pages
                .checked_mul(host::page().length().0.get())
                .expect("the bytes fit a word"),
        )
    }

    /// The bytes that the process maps, from the task's basic information.
    ///
    /// # Specification
    /// trivial.
    #[cfg(target_os = "macos")]
    fn mapped() -> Bytes
    {
        /// `mach_task_basic_info`, packed to 4 bytes as the system's header
        /// packs it.
        #[repr(C, packed(4))]
        #[derive(Default)]
        struct Basic
        {
            /// The bytes that the task maps.
            virtual_size: u64,
            /// The bytes that the task holds in memory.
            resident_size: u64,
            /// The most bytes that the task held in memory.
            resident_size_max: u64,
            /// The user time of the task's ended threads.
            user_time: [i32; 2],
            /// The system time of the task's ended threads.
            system_time: [i32; 2],
            /// The task's scheduling policy.
            policy: i32,
            /// The count of the task's suspensions.
            suspend_count: i32,
        }
        /// A port, a flavour, a count of words or an answer of the kernel.
        ///
        /// # Specification
        /// trivial.
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct Word(u32);
        /// The kernel's reads of a task.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: the port names a live task, and the record and
        ///   the count are the call's to write.
        #[expect(
            unused_doc_comments,
            reason = "the policy lint reads this block's safety section; rustdoc renders none on an extern block"
        )]
        unsafe extern "C" {
            /// The port of the calling task.
            static mach_task_self_: Word;
            /// The kernel's information about a task.
            ///
            /// # Specification
            /// trivial.
            fn task_info(
                task: Word,
                flavor: Word,
                information: *mut Basic,
                count: *mut Word,
            ) -> Word;
        }
        /// The flavour of `mach_task_basic_info`.
        const MACH_TASK_BASIC_INFO: Word = Word(20);
        /// The header's count of the record: its 48 bytes in 4-byte words.
        const MACH_TASK_BASIC_INFO_COUNT: Word = Word(12);
        let mut basic = Basic::default();
        let mut count = MACH_TASK_BASIC_INFO_COUNT;
        // SAFETY: the task port names this process, and the record and the
        // count are the call's to write.
        let answer = unsafe {
            task_info(
                mach_task_self_,
                MACH_TASK_BASIC_INFO,
                &raw mut basic,
                &raw mut count,
            )
        };
        assert_eq!(Word(0), answer, "task_info answers");
        Bytes(usize::try_from(basic.virtual_size).expect("the size fits a word"))
    }

    /// 10000 blocks of mixed sizes, from one byte to past a page, each
    /// filled and checked, and freed in a mixed order. The process maps more
    /// while the heap holds its runs, and as many bytes after the heap ends
    /// as before it started.
    #[test]
    fn mixed_blocks_leave_the_mapped_pages_as_they_were()
    {
        let page = host::page();
        let mut blocks: Vec<(Base, Layout, u8)> = Vec::with_capacity(10_000);
        let before = mapped();
        let heap = Heap::new(page);
        let mut seed = 0x2545_F491_u32;
        for mark in (1_u8 ..= 255).cycle().take(10_000) {
            seed ^= seed << 13_u32;
            seed ^= seed >> 17_u32;
            seed ^= seed << 5_u32;
            let size = 1 + usize::try_from(seed % (1 << ((seed >> 28_u32) % 15)))
                .expect("a size fits a word");
            let layout = Layout::from_size_align(size, 8).expect("a layout");
            let block = heap
                .allocate(layout)
                .expect("the heap gives a block")
                .base();
            // SAFETY: the block holds at least `size` writable bytes.
            unsafe {
                block.0.as_ptr().write_bytes(mark, size);
            }
            blocks.push((block, layout, mark));
        }
        let during = mapped();
        for &(block, layout, mark) in &blocks {
            // SAFETY: the block holds at least `layout.size()` readable bytes.
            let bytes = unsafe { core::slice::from_raw_parts(block.0.as_ptr(), layout.size()) };
            assert!(bytes.iter().all(|&byte| byte == mark), "{layout:?}");
        }
        // 7919 is prime and divides no power of ten, so the stride visits
        // each block once in a mixed order.
        for step in 0 .. blocks.len() {
            let (block, layout, _) = blocks[step * 7919 % blocks.len()];
            // SAFETY: the heap gave the block for its layout, and the test
            // keeps no reference into it.
            unsafe { heap.free(block, layout) }.expect("the heap takes the block back");
        }
        drop(heap);
        let after = mapped();
        assert!(
            during > before,
            "the heap maps runs: {before:?} then {during:?}"
        );
        assert_eq!(before, after, "the heap gives each run back");
    }
}
