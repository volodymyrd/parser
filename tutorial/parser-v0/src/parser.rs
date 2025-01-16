pub trait Parser<'i> {
    type Output;
    type Error;

    #[inline]
    fn parse(&mut self, input: &'i str) -> Result<Self::Output, Self::Error> {
        self.process(input)
    }

    fn process(&mut self, input: &'i str) -> Result<Self::Output, Self::Error>;
}
