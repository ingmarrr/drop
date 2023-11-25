pub fn run() {
    tilog::init_logger(
        tilog::Config::default()
            .with_level(tilog::Level::Debug)
            .with_emoji(true),
    );
    tilog::info!("Running Program");
}
