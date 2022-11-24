use anyhow::{anyhow, Context, Result};
use strum::IntoEnumIterator;
use strum_macros::{AsRefStr, EnumIter};

/// The semantics associated with a problem.
#[derive(Debug, Clone, Copy, PartialEq, Eq, AsRefStr, EnumIter)]
pub enum Semantics {
    /// The grounded semantics
    GR,
    /// The complete semantics
    CO,
    /// The preferred semantics
    PR,
    /// The stable semantics
    ST,
    /// The semi-stable semantics
    SST,
    /// The stage semantics
    STG,
    /// The ideal semantics
    ID,
}

impl TryFrom<&str> for Semantics {
    type Error = anyhow::Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value.to_ascii_lowercase().as_str() {
            "gr" => Ok(Semantics::GR),
            "co" => Ok(Semantics::CO),
            "pr" => Ok(Semantics::PR),
            "st" => Ok(Semantics::ST),
            "sst" => Ok(Semantics::SST),
            "stg" => Ok(Semantics::STG),
            "id" => Ok(Semantics::ID),
            _ => Err(anyhow!(r#"undefined semantics "{}""#, value)),
        }
    }
}

/// The query to compute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, AsRefStr, EnumIter)]
pub enum Query {
    /// Compute a single extension
    SE,
    /// Check credulous acceptance
    DC,
    /// Check skeptical acceptance
    DS,
}

impl Query {
    /// Reads a string depicting a problem with an XX-YY pattern.
    ///
    /// This functions reads a problem string following the format in ICCMA competitions.
    /// The string is split at the first hyphen found in it.
    /// The substring before this hyphen is considered as the query, while the substring after it is considered as the semantics.
    ///
    /// In case there is no hyphen, an error is returned.
    /// In case there is more then one, then all the hyphen,s except the first are considered as part of the semantics.
    pub fn read_problem_string(problem: &str) -> Result<(Query, Semantics)> {
        let context = || format!(r#"while parsing problem string "{}""#, problem);
        match problem.find('-') {
            Some(n) => {
                let query = Query::try_from(&problem[0..n]).with_context(context)?;
                let semantics = Semantics::try_from(&problem[1 + n..]).with_context(context)?;
                Ok((query, semantics))
            }
            None => Err(anyhow!("no hyphen in problem string")).with_context(context),
        }
    }

    /// Returns an iterator through the known problems given as strings.
    ///
    /// This functions returns strings representing the problems as defined in ICCMA competitions.
    /// Each string is composed by the query, an hyphen, and the semantics.
    /// The queries and problems are given by the sequences of strings representing them in the competitions.
    pub fn iter_problem_strings() -> impl Iterator<Item = String> + 'static {
        Semantics::iter()
            .flat_map(|sem| Query::iter().map(move |q| format!("{}-{}", q.as_ref(), sem.as_ref())))
    }
}

impl TryFrom<&str> for Query {
    type Error = anyhow::Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value.to_ascii_lowercase().as_str() {
            "se" => Ok(Query::SE),
            "dc" => Ok(Query::DC),
            "ds" => Ok(Query::DS),
            _ => Err(anyhow!(r#"undefined query "{}""#, value)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_problem_ok() {
        assert_eq!(
            (Query::SE, Semantics::ST),
            Query::read_problem_string("SE-ST").unwrap()
        );
        assert_eq!(
            (Query::SE, Semantics::ST),
            Query::read_problem_string("se-st").unwrap()
        );
    }

    #[test]
    fn test_read_problem_unknown_query() {
        assert!(Query::read_problem_string("foo-ST").is_err());
    }

    #[test]
    fn test_read_problem_unknown_semantics() {
        assert!(Query::read_problem_string("SE-foo").is_err());
    }

    #[test]
    fn test_read_problem_no_hyphen() {
        assert!(Query::read_problem_string("SEST").is_err());
    }

    #[test]
    fn test_iter_as_strings() {
        let mut expected = [
            "DC-CO", "DC-GR", "DC-ID", "DC-PR", "DC-SST", "DC-ST", "DC-STG", "DS-CO", "DS-GR",
            "DS-ID", "DS-PR", "DS-SST", "DS-ST", "DS-STG", "SE-CO", "SE-GR", "SE-ID", "SE-PR",
            "SE-SST", "SE-ST", "SE-STG",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<String>>();
        expected.sort_unstable();
        let mut actual = Query::iter_problem_strings().collect::<Vec<String>>();
        actual.sort_unstable();
        assert_eq!(expected, actual)
    }
}
