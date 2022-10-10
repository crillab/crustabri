use anyhow::{anyhow, Context, Result};

/// The semantics associated with a problem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Semantics {
    /// The grounded semantics
    GR,
    /// The complete semantics
    CO,
    /// The stable semantics
    ST,
}

impl TryFrom<&str> for Semantics {
    type Error = anyhow::Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value.to_ascii_lowercase().as_str() {
            "gr" => Ok(Semantics::GR),
            "co" => Ok(Semantics::CO),
            "st" => Ok(Semantics::ST),
            _ => Err(anyhow!(r#"undefined semantics "{}""#, value)),
        }
    }
}

/// The query to compute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Query {
    /// Compute a single extension
    SE,
    /// Check credulous acceptance
    DC,
    /// Check skeptical acceptance
    DS,
}

impl Query {
    /// Returns a short string representing the query.
    ///
    /// The string corresponds to the two letters query as defined in ICCMA competitions.
    pub fn to_short_str(&self) -> &str {
        match self {
            Query::SE => "SE",
            Query::DC => "DC",
            Query::DS => "DS",
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_problem_ok() {
        assert_eq!(
            (Query::SE, Semantics::ST),
            read_problem_string("SE-ST").unwrap()
        );
        assert_eq!(
            (Query::SE, Semantics::ST),
            read_problem_string("se-st").unwrap()
        );
    }

    #[test]
    fn test_read_problem_unknown_query() {
        assert!(read_problem_string("foo-ST").is_err());
    }

    #[test]
    fn test_read_problem_unknown_semantics() {
        assert!(read_problem_string("SE-foo").is_err());
    }

    #[test]
    fn test_read_problem_no_hyphen() {
        assert!(read_problem_string("SEST").is_err());
    }
}
