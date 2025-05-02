use static_toml::static_toml;

static_toml! {
    pub const COSTS = include_toml!("costs.toml");
}
