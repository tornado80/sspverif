use std::io::{Result, Write};

pub trait SmtFmt {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()>;

    fn to_string(&self) -> String {
        let mut buf = vec![];
        self.write_smt_to(&mut buf)
            .expect("can't happen, we assume the buffer never errors");

        String::from_utf8(buf).expect("can't happen, we only write utf8")
    }
}
