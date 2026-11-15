#[cfg(test)]
mod test
{
    use crate::sys::linux::uapi::arch::io_uring_params;
    use crate::sys::linux::uapi::io_uring::io_uring_setup;

    #[test]
    fn setup() -> std::io::Result<()>
    {
        let entries = 2u32;
        let mut params = io_uring_params::default();
        let fd = { io_uring_setup(entries, &mut params) }?;
        drop(fd);
        Ok(())
    }
}
