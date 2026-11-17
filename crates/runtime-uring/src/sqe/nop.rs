//! The preparers of the operation that does nothing.

/// The preparers, as methods of the submission entry.
pub mod repr
{
    use crate::sqe::repr::Sqe64;

    impl Sqe64<'_>
    {
        /// Prepares the entry for an operation that does nothing and posts one
        /// completion.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: The owner's crate marks each preparer `unsafe`.
        ///   This one reads no pointer and names no descriptor, so it holds no
        ///   invariant of its own.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_nop(&mut self)
        {
            let sqe = &raw mut *self.sqe();
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_prep_nop(sqe);
            }
        }
    }
}

// #[cfg(test)]
// pub(crate) mod test {
//     use crate::IoUring;

//     pub fn terminate<S, C>(ring: &mut IoUring<'_, S, C>)
//     where
//         C: crate::cqe::Kind,
//         S: crate::sqe::Kind,
//     {
//         const REQ_NOP: u64 = u64::MAX - 1;

//         let mut sq = ring.squeue();
//         let mut sqe = sq.get_sqe().unwrap();
//         unsafe { sqe.prep_nop() };
//         unsafe { sqe.set_data64(REQ_NOP) };

//         let num = sq.submit().unwrap();
//         assert_eq!(1, num);

//         let mut cq = ring.cqueue();
//         let cqe = cq.wait(1).unwrap().next().unwrap().into();
//         assert_eq!(cqe.cqe().user_data, REQ_NOP);
//     }
// }
