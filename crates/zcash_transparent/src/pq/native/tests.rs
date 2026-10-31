mod fast {
    use super::super::*;
    use crate::pq::sha2_128f as crypto;
    const PARAMETERS: ParameterSet = ParameterSet::Sha2_128f;
    include!("tests/cases.rs");
}
mod small {
    use super::super::*;
    use crate::pq::sha2_192s as crypto;
    const PARAMETERS: ParameterSet = ParameterSet::Sha2_192s;
    include!("tests/cases.rs");
}
