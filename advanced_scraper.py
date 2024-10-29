import streamlit as st
import asyncio
import aiohttp
import logging
import json
import csv
import io
import random
import hashlib
import os
import re
import yaml
import threading
import schedule
import time
import pandas as pd
from datetime import datetime, timedelta
from pathlib import Path
from bs4 import BeautifulSoup, Comment
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import ChromeOptions
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from webdriver_manager.chrome import ChromeDriverManager
from fake_useragent import UserAgent
from urllib.parse import urljoin, urlparse
from urllib.robotparser import RobotFileParser
from PIL import Image
from io import BytesIO
import validators
from newspaper import Article
import nltk
from dataclasses import dataclass
from typing import Optional, List, Dict
import xml.etree.ElementTree as ET

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('scraper.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)


@dataclass
class ScrapingConfig:
    """Configuration for scraping tasks"""
    max_depth: int = 2
    max_pages: int = 100
    respect_robots: bool = True
    follow_links: bool = False
    user_agent: Optional[str] = None
    timeout: int = 30
    max_retries: int = 3
    delay: float = 1.0
    screenshot: bool = False
    save_html: bool = False
    extract_metadata: bool = True
    extract_comments: bool = True
    extract_structured_data: bool = True
    max_connections: int = 100
    requests_per_second: int = 10
    cache_size: int = 1000
    cache_ttl: int = 24  # hours


class RateLimiter:
    def __init__(self, requests_per_second=10):
        self.rate = requests_per_second
        self.last_check = time.time()
        self.tokens = requests_per_second
        self._lock = asyncio.Lock()
        self.domain_limiters = {}

    async def acquire(self, domain=None):
        """Acquire a token using token bucket algorithm"""
        if domain:
            if domain not in self.domain_limiters:
                self.domain_limiters[domain] = {
                    'tokens': self.rate,
                    'last_check': time.time()
                }
            return await self._acquire_domain(domain)

        async with self._lock:
            now = time.time()
            time_passed = now - self.last_check
            self.tokens = min(
                self.rate,
                self.tokens + time_passed * self.rate
            )

            if self.tokens < 1:
                await asyncio.sleep(1 / self.rate)
                self.tokens = 1

            self.tokens -= 1
            self.last_check = now

    async def _acquire_domain(self, domain):
        """Acquire a token for specific domain"""
        async with self._lock:
            now = time.time()
            limiter = self.domain_limiters[domain]
            time_passed = now - limiter['last_check']
            limiter['tokens'] = min(
                self.rate,
                limiter['tokens'] + time_passed * self.rate
            )

            if limiter['tokens'] < 1:
                await asyncio.sleep(1 / self.rate)
                limiter['tokens'] = 1

            limiter['tokens'] -= 1
            limiter['last_check'] = now


class ResourceManager:
    def __init__(self, max_connections=100):
        self.active_connections = 0
        self.max_connections = max_connections
        self._lock = asyncio.Lock()

    async def acquire(self):
        """Acquire a connection slot"""
        async with self._lock:
            while self.active_connections >= self.max_connections:
                await asyncio.sleep(0.1)
            self.active_connections += 1

    async def release(self):
        """Release a connection slot"""
        async with self._lock:
            self.active_connections -= 1


class RetryHandler:
    def __init__(self, max_retries=3, base_delay=1):
        self.max_retries = max_retries
        self.base_delay = base_delay

    def get_delay(self, attempt):
        """Implement exponential backoff"""
        return self.base_delay * (2 ** attempt)

    async def execute_with_retry(self, func, *args, **kwargs):
        """Execute function with retry logic"""
        last_exception = None

        for attempt in range(self.max_retries):
            try:
                return await func(*args, **kwargs)
            except Exception as e:
                last_exception = e
                if attempt < self.max_retries - 1:
                    delay = self.get_delay(attempt)
                    logger.warning(f"Attempt {attempt + 1} failed: {str(e)}. Retrying in {delay}s")
                    await asyncio.sleep(delay)
                else:
                    logger.error(f"All retry attempts failed: {str(e)}")
                    raise last_exception


class ScraperMetrics:
    def __init__(self):
        self.metrics = {
            'requests_total': 0,
            'successful_requests': 0,
            'failed_requests': 0,
            'bytes_downloaded': 0,
            'response_times': [],
            'errors_by_type': {},
            'cache_hits': 0,
            'cache_misses': 0
        }
        self._lock = threading.Lock()

    def record_request(self, success: bool, response_time: float, bytes_downloaded: int, error_type: str = None):
        """Record metrics for a request"""
        with self._lock:
            self.metrics['requests_total'] += 1
            if success:
                self.metrics['successful_requests'] += 1
            else:
                self.metrics['failed_requests'] += 1
                if error_type:
                    self.metrics['errors_by_type'][error_type] = \
                        self.metrics['errors_by_type'].get(error_type, 0) + 1

            self.metrics['bytes_downloaded'] += bytes_downloaded
            self.metrics['response_times'].append(response_time)

    def record_cache_hit(self):
        """Record cache hit"""
        with self._lock:
            self.metrics['cache_hits'] += 1

    def record_cache_miss(self):
        """Record cache miss"""
        with self._lock:
            self.metrics['cache_misses'] += 1

    def get_statistics(self) -> dict:
        """Get statistical summary of metrics"""
        with self._lock:
            response_times = self.metrics['response_times']
            return {
                'total_requests': self.metrics['requests_total'],
                'success_rate': (self.metrics['successful_requests'] /
                                 max(1, self.metrics['requests_total']) * 100),
                'avg_response_time': sum(response_times) / max(1, len(response_times)),
                'total_bytes_downloaded': self.metrics['bytes_downloaded'],
                'error_distribution': self.metrics['errors_by_type'],
                'cache_hit_rate': (self.metrics['cache_hits'] /
                                   max(1, self.metrics['cache_hits'] + self.metrics['cache_misses']) * 100)
            }


class EnhancedDataValidator:
    @staticmethod
    def clean_text(text):
        """Clean and normalize text data"""
        if not text:
            return ""
        text = re.sub(r'\s+', ' ', text.strip())
        text = re.sub(r'[^\w\s.,!?-]', '', text)
        return text

    @staticmethod
    def validate_url(url):
        """Validate URL format"""
        return validators.url(url)

    @staticmethod
    def validate_email(email):
        """Validate email format"""
        return validators.email(email)

    @staticmethod
    def clean_html(html):
        """Clean HTML content"""
        soup = BeautifulSoup(html, 'html.parser')
        for element in soup(['script', 'style', 'iframe']):
            element.decompose()
        return str(soup)

    @staticmethod
    def sanitize_filename(filename):
        """Sanitize filename for safe saving"""
        return re.sub(r'[^\w\-_.]', '_', filename)

    def validate_content(self, content: dict) -> tuple[bool, list]:
        """Validate scraped content structure and data types"""
        errors = []
        required_fields = {'url', 'timestamp', 'content_type', 'data'}

        # Check required fields
        missing_fields = required_fields - set(content.keys())
        if missing_fields:
            errors.append(f"Missing required fields: {missing_fields}")

        # Validate URL
        if not self.validate_url(content.get('url', '')):
            errors.append("Invalid URL format")

        # Validate timestamp
        try:
            datetime.fromisoformat(content.get('timestamp', ''))
        except ValueError:
            errors.append("Invalid timestamp format")

        return len(errors) == 0, errors


class ContentExtractor:
    def __init__(self):
        try:
            nltk.data.find('tokenizers/punkt')
        except LookupError:
            nltk.download('punkt')

    def extract_article(self, url: str) -> dict:
        """Extract article content using newspaper3k"""
        try:
            article = Article(url)
            article.download()
            article.parse()
            article.nlp()

            return {
                'title': article.title,
                'text': article.text,
                'summary': article.summary,
                'keywords': article.keywords,
                'authors': article.authors,
                'publish_date': article.publish_date,
                'top_image': article.top_image,
                'images': list(article.images),
                'movies': list(article.movies)
            }
        except Exception as e:
            logger.error(f"Error extracting article content: {str(e)}")
            return {}

    def extract_metadata(self, soup: BeautifulSoup) -> dict:
        """Extract metadata from HTML"""
        metadata = {
            'meta_tags': {},
            'links': {},
            'scripts': [],
            'comments': [],
            'structured_data': []
        }

        # Extract meta tags
        for meta in soup.find_all('meta'):
            name = meta.get('name') or meta.get('property')
            if name:
                metadata['meta_tags'][name] = meta.get('content')

        # Extract links with rel attributes
        for link in soup.find_all('link'):
            rel = link.get('rel')
            if rel:
                metadata['links'][str(rel)] = link.get('href')

        # Extract comments
        metadata['comments'] = [str(comment) for comment in
                                soup.find_all(string=lambda text: isinstance(text, Comment))]

        # Extract JSON-LD structured data
        for script in soup.find_all('script', type='application/ld+json'):
            try:
                metadata['structured_data'].append(json.loads(script.string))
            except:
                continue

        return metadata


class WebScraper:
    def __init__(self):
        self.session_data = {}
        self.history = []
        self.config = ScrapingConfig()
        self.user_agent = UserAgent()
        self.metrics = ScraperMetrics()
        self.validator = EnhancedDataValidator()
        self.content_extractor = ContentExtractor()
        self.rate_limiter = RateLimiter(self.config.requests_per_second)
        self.resource_manager = ResourceManager(self.config.max_connections)
        self.retry_handler = RetryHandler(self.config.max_retries)
        self.init_cache()

    def init_cache(self):
        """Initialize cache with TTL and size limits"""
        self.cache = {
            'data': {},
            'size': 0,
            'max_size': self.config.cache_size
        }

    def cache_cleanup(self):
        """Remove oldest cached items when cache exceeds threshold"""
        if len(self.cache['data']) > (self.cache['max_size'] * 0.8):
            sorted_cache = sorted(
                self.cache['data'].items(),
                key=lambda x: x[1]['timestamp']
            )
            to_remove = sorted_cache[:int(self.cache['max_size'] * 0.2)]
            for key, _ in to_remove:
                del self.cache['data'][key]

    async def create_client_session(self):
        """Create an optimized aiohttp client session"""
        connector = aiohttp.TCPConnector(
            limit=self.config.max_connections,
            ttl_dns_cache=300,
            use_dns_cache=True
        )
        return aiohttp.ClientSession(
            connector=connector,
            timeout=aiohttp.ClientTimeout(total=self.config.timeout),
            headers={'User-Agent': self.config.user_agent or self.user_agent.random}
        )

    def get_chrome_driver(self):
        """Get configured Chrome WebDriver instance"""
        chrome_options = ChromeOptions()
        chrome_options.add_argument('--no-sandbox')
        chrome_options.add_argument('--headless')
        chrome_options.add_argument('--disable-dev-shm-usage')

        if self.config.user_agent:
            chrome_options.add_argument(f'--user-agent={self.config.user_agent}')
        else:
            chrome_options.add_argument(f'--user-agent={self.user_agent.random}')

        service = Service(ChromeDriverManager().install())
        return webdriver.Chrome(service=service, options=chrome_options)

    async def scrape_website(self, url: str, content_type: str, form_selector: str = None,
                             login_required: bool = False, login_details: dict = None) -> dict:
        """Enhanced main scraping function with async support"""
        if not self.validator.validate_url(url):
            raise ValueError("Invalid URL format")

        if not self.check_robots_txt(url):
            raise ValueError("Scraping not allowed by robots.txt")

        # Check cache first
        cached_content = self.load_from_cache(url)
        if cached_content and not login_required:
            self.metrics.record_cache_hit()
            return cached_content

        self.metrics.record_cache_miss()

        # Initialize progress tracking
        progress_bar = st.progress(0)
        status_text = st.empty()

        start_time = time.time()

        try:
            await self.rate_limiter.acquire(urlparse(url).netloc)
            await self.resource_manager.acquire()

            status_text.text("Initializing)
            driver = self.get_chrome_driver()
            status_text.text(f"Connected! Navigating to {url}...")
            progress_bar.progress(30)

            try:
                if login_required and login_details:
                    status_text.text("Attempting login...")
                    login_success = await self.handle_login(
                        driver,
                        login_details['login_url'],
                        login_details['username_selector'],
                        login_details['password_selector'],
                        login_details['submit_selector'],
                        login_details['username'],
                        login_details['password']
                    )
                    if not login_success:
                        raise Exception("Login failed")

                driver.get(url)
                await asyncio.sleep(random.uniform(1, 3))  # Random delay
                html = driver.page_source

                status_text.text('Page loaded. Scraping content...')
                progress_bar.progress(50)

                # Initialize result dictionary
                result = {
                    'url': url,
                    'timestamp': datetime.now().isoformat(),
                    'content_type': content_type,
                    'data': None,
                    'metadata': None,
                    'screenshots': [],
                    'html_path': None
                }

                # Capture screenshot if enabled
                if self.config.screenshot:
                    screenshot_path = await self.capture_screenshot(driver, url)
                    if screenshot_path:
                        result['screenshots'].append(screenshot_path)

                # Save HTML if enabled
                if self.config.save_html:
                    html_dir = "saved_html"
                    os.makedirs(html_dir, exist_ok=True)
                    html_path = os.path.join(
                        html_dir,
                        f"{self.validator.sanitize_filename(urlparse(url).netloc)}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.html"
                    )
                    with open(html_path, 'w', encoding='utf-8') as f:
                        f.write(html)
                    result['html_path'] = html_path

                # Extract content based on type
                soup = BeautifulSoup(html, 'html.parser')

                if content_type == 'webform':
                    result['data'] = await self.scrape_webform(driver, form_selector)
                elif content_type == 'text':
                    result['data'] = soup.get_text(separator='\n', strip=True)
                elif content_type == 'links':
                    result['data'] = [{'text': a.text, 'href': a.get('href')}
                                      for a in soup.find_all('a', href=True)]
                elif content_type == 'images':
                    result['data'] = [{'alt': img.get('alt', ''), 'src': img.get('src')}
                                      for img in soup.find_all('img', src=True)]
                elif content_type == 'tables':
                    result['data'] = [pd.read_html(str(table))[0].to_dict('records')
                                      for table in soup.find_all('table')]
                elif content_type == 'dynamic':
                    await asyncio.sleep(5)
                    result['data'] = await self.extract_dynamic_content(driver)
                elif content_type == 'article':
                    result['data'] = self.content_extractor.extract_article(url)

                # Extract metadata if enabled
                if self.config.extract_metadata:
                    result['metadata'] = self.content_extractor.extract_metadata(soup)

                # Validate the scraped content
                is_valid, errors = self.validator.validate_content(result)
                if not is_valid:
                    logger.warning(f"Content validation errors: {errors}")
                    result['validation_errors'] = errors

                # Save to cache if successful and not login-required
                if not login_required:
                    self.save_to_cache(url, result)

                # Record metrics
                self.metrics.record_request(
                    success=True,
                    response_time=time.time() - start_time,
                    bytes_downloaded=len(str(result))
                )

                # Add to history
                self.history.append({
                    'url': url,
                    'timestamp': datetime.now().isoformat(),
                    'content_type': content_type,
                    'success': True
                })

                progress_bar.progress(100)
                status_text.text('Scraping completed successfully!')

                return result

            except Exception as e:
                logger.error(f"Error during scraping: {str(e)}")
                self.metrics.record_request(
                    success=False,
                    response_time=time.time() - start_time,
                    bytes_downloaded=0,
                    error_type=type(e).__name__
                )
                self.history.append({
                    'url': url,
                    'timestamp': datetime.now().isoformat(),
                    'content_type': content_type,
                    'success': False,
                    'error': str(e)
                })
                raise e
            finally:
                driver.quit()
                await self.resource_manager.release()

            async def handle_login(self, driver, login_url, username_selector, password_selector,
                                   submit_selector, username, password):
                """Enhanced login handling with retry support"""
                try:
                    driver.get(login_url)
                    username_field = WebDriverWait(driver, 10).until(
                        EC.presence_of_element_located((By.CSS_SELECTOR, username_selector))
                    )
                    password_field = WebDriverWait(driver, 10).until(
                        EC.presence_of_element_located((By.CSS_SELECTOR, password_selector))
                    )
                    submit_button = WebDriverWait(driver, 10).until(
                        EC.presence_of_element_located((By.CSS_SELECTOR, submit_selector))
                    )

                    username_field.clear()
                    username_field.send_keys(username)
                    password_field.clear()
                    password_field.send_keys(password)
                    submit_button.click()

                    await asyncio.sleep(3)  # Wait for login to complete

                    # Verify login success (can be customized based on site)
                    if "error" in driver.current_url.lower() or "login" in driver.current_url.lower():
                        return False

                    return True
                except Exception as e:
                    logger.error(f"Login failed: {str(e)}")
                    return False

            async def scrape_webform(self, driver, form_selector):
                """Enhanced webform scraping"""
                try:
                    form = WebDriverWait(driver, 10).until(
                        EC.presence_of_element_located((By.CSS_SELECTOR, form_selector))
                    )

                    form_data = {
                        'inputs': [],
                        'selects': [],
                        'textareas': [],
                        'buttons': []
                    }

                    # Extract input fields
                    for input_elem in form.find_elements(By.TAG_NAME, 'input'):
                        input_data = {
                            'name': input_elem.get_attribute('name'),
                            'type': input_elem.get_attribute('type'),
                            'id': input_elem.get_attribute('id'),
                            'class': input_elem.get_attribute('class'),
                            'placeholder': input_elem.get_attribute('placeholder'),
                            'value': input_elem.get_attribute('value'),
                            'required': input_elem.get_attribute('required') is not None
                        }
                        form_data['inputs'].append(input_data)

                    # Extract select fields
                    for select_elem in form.find_elements(By.TAG_NAME, 'select'):
                        options = []
                        for option in select_elem.find_elements(By.TAG_NAME, 'option'):
                            options.append({
                                'value': option.get_attribute('value'),
                                'text': option.text,
                                'selected': option.is_selected()
                            })

                        select_data = {
                            'name': select_elem.get_attribute('name'),
                            'id': select_elem.get_attribute('id'),
                            'class': select_elem.get_attribute('class'),
                            'required': select_elem.get_attribute('required') is not None,
                            'options': options
                        }
                        form_data['selects'].append(select_data)

                    # Extract textareas
                    for textarea in form.find_elements(By.TAG_NAME, 'textarea'):
                        textarea_data = {
                            'name': textarea.get_attribute('name'),
                            'id': textarea.get_attribute('id'),
                            'class': textarea.get_attribute('class'),
                            'placeholder': textarea.get_attribute('placeholder'),
                            'value': textarea.get_attribute('value'),
                            'required': textarea.get_attribute('required') is not None
                        }
                        form_data['textareas'].append(textarea_data)

                    # Extract buttons
                    for button in form.find_elements(By.TAG_NAME, 'button'):
                        button_data = {
                            'type': button.get_attribute('type'),
                            'text': button.text,
                            'id': button.get_attribute('id'),
                            'class': button.get_attribute('class')
                        }
                        form_data['buttons'].append(button_data)

                    return form_data
                except Exception as e:
                    logger.error(f"Error scraping webform: {str(e)}")
                    return None

            async def capture_screenshot(self, driver, url):
                """Enhanced screenshot capture with error handling"""
                try:
                    screenshot = driver.get_screenshot_as_png()
                    image = Image.open(BytesIO(screenshot))

                    # Create screenshots directory if it doesn't exist
                    os.makedirs('screenshots', exist_ok=True)

                    # Generate filename
                    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
                    filename = f"screenshots/{self.validator.sanitize_filename(urlparse(url).netloc)}_{timestamp}.png"

                    # Save image with optimization
                    image.save(filename, optimize=True, quality=85)
                    return filename
                except Exception as e:
                    logger.error(f"Screenshot capture failed: {str(e)}")
                    return None

            def save_to_cache(self, url, content):
                """Enhanced cache saving with cleanup"""
                try:
                    self.cache_cleanup()  # Clean up old entries if needed

                    url_hash = hashlib.md5(url.encode()).hexdigest()
                    self.cache['data'][url_hash] = {
                        'content': content,
                        'timestamp': datetime.now().isoformat(),
                        'expires': (datetime.now() + timedelta(hours=self.config.cache_ttl)).isoformat()
                    }
                except Exception as e:
                    logger.error(f"Error saving to cache: {str(e)}")

            def load_from_cache(self, url):
                """Enhanced cache loading with expiration check"""
                try:
                    url_hash = hashlib.md5(url.encode()).hexdigest()
                    cached_data = self.cache['data'].get(url_hash)

                    if cached_data:
                        expires = datetime.fromisoformat(cached_data['expires'])
                        if datetime.now() < expires:
                            return cached_data['content']
                        else:
                            del self.cache['data'][url_hash]

                    return None
                except Exception as e:
                    logger.error(f"Error loading from cache: {str(e)}")
                    return None

            def get_metrics(self):
                """Get current scraping metrics"""
                return self.metrics.get_statistics()

            def clear_history(self):
                """Clear scraping history"""
                self.history = []

            def export_history(self, format='json'):
                """Export scraping history in various formats"""
                return export_data(self.history, format)

            # Initialize the scraper
            scraper = WebScraper()

            # Streamlit UI
            def main():
                st.title("Enhanced Web Scraper")
                st.write("Advanced web scraping tool with improved performance and features")

                # Sidebar configuration
                with st.sidebar:
                    st.header("Configuration")

                    # Basic Settings
                    st.subheader("Basic Settings")
                    max_depth = st.slider("Max Crawl Depth", 1, 10, 2)
                    max_pages = st.number_input("Max Pages", 1, 1000, 100)
                    respect_robots = st.checkbox("Respect robots.txt", value=True)

                    # Performance Settings
                    st.subheader("Performance")
                    max_connections = st.slider("Max Connections", 10, 200, 100)
                    requests_per_second = st.slider("Requests/Second", 1, 20, 10)

                    # Cache Settings
                    st.subheader("Cache Settings")
                    cache_enabled = st.checkbox("Enable Cache", value=True)
                    if cache_enabled:
                        cache_ttl = st.slider("Cache TTL (hours)", 1, 72, 24)
                        cache_size = st.slider("Cache Size", 100, 5000, 1000)

                    # Update configuration
                    if st.button("Update Configuration"):
                        scraper.config = ScrapingConfig(
                            max_depth=max_depth,
                            max_pages=max_pages,
                            respect_robots=respect_robots,
                            max_connections=max_connections,
                            requests_per_second=requests_per_second,
                            cache_ttl=cache_ttl if cache_enabled else 0,
                            cache_size=cache_size if cache_enabled else 0
                        )
                        st.success("Configuration updated!")

                    # Show current metrics
                    st.subheader("Current Metrics")
                    metrics = scraper.get_metrics()
                    st.write(f"Total Requests: {metrics['total_requests']}")
                    st.write(f"Success Rate: {metrics['success_rate']:.2f}%")
                    st.write(f"Avg Response Time: {metrics['avg_response_time']:.2f}s")
                    if cache_enabled:
                        st.write(f"Cache Hit Rate: {metrics['cache_hit_rate']:.2f}%")

                # Main content area
                url = st.text_input("Enter Website URL")
                content_type = st.selectbox(
                    "Select Content Type",
                    ['text', 'links', 'images', 'tables', 'webform', 'dynamic', 'article']
                )

                form_selector = None
                if content_type == 'webform':
                    form_selector = st.text_input("Form Selector", value="form")

                if st.button("Start Scraping"):
                    if url:
                        try:
                            with st.spinner("Scraping in progress..."):
                                result = asyncio.run(scraper.scrape_website(
                                    url, content_type, form_selector
                                ))

                            # Display results
                            st.subheader("Scraping Results")

                            # Show main content
                            if content_type == 'text':
                                st.text_area("Extracted Text", result['data'], height=300)
                            else:
                                st.json(result['data'])

                            # Show metadata if available
                            if result.get('metadata'):
                                with st.expander("Metadata"):
                                    st.json(result['metadata'])

                            # Show screenshots if available
                            if result.get('screenshots'):
                                st.subheader("Screenshots")
                                for screenshot in result['screenshots']:
                                    st.image(screenshot)

                                    # Export options
                                    st.subheader("Export Options")
                                    export_format = st.selectbox(
                                        "Select export format",
                                        ['json', 'csv', 'txt']
                                    )

                                    exported_data = export_data(result, export_format)
                                    st.download_button(
                                        label=f"Download as {export_format.upper()}",
                                        data=exported_data,
                                        file_name=f"scraped_data_{datetime.now().strftime('%Y%m%d_%H%M%S')}.{export_format}",
                                        mime=f"text/{export_format}"
                                    )

                                    # Display validation warnings if any
                                    if 'validation_errors' in result:
                                        st.warning("Validation Warnings:")
                                        for error in result['validation_errors']:
                                            st.write(f"- {error}")

                                except Exception as e:
                                st.error(f"Scraping failed: {str(e)}")
                            else:
                                st.warning("Please enter a URL to scrape.")

                        # Batch Scraping Section
                        st.header("Batch Scraping")
                        with st.expander("Batch Scraping Options"):
                            batch_urls = st.text_area(
                                "Enter URLs (one per line)",
                                height=100,
                                help="Enter multiple URLs to scrape, one URL per line"
                            )

                            batch_content_type = st.selectbox(
                                "Select content type for batch scraping",
                                ['text', 'links', 'images', 'tables', 'article'],
                                key="batch_content_type"
                            )

                            if st.button("Start Batch Scraping"):
                                urls = [url.strip() for url in batch_urls.split('\n') if url.strip()]
                                if urls:
                                    with st.spinner("Batch scraping in progress..."):
                                        try:
                                            results = asyncio.run(scraper.async_scrape(urls))
                                            st.session_state['batch_results'] = results
                                            st.success(f"Successfully scraped {len(results)} URLs!")

                                            # Display batch results
                                            for i, result in enumerate(results):
                                                with st.expander(f"Result {i + 1}: {result.url}"):
                                                    if result.success:
                                                        st.json(result.content)
                                                    else:
                                                        st.error(f"Failed: {result.error}")
                                        except Exception as e:
                                            st.error(f"Batch scraping failed: {str(e)}")
                                else:
                                    st.warning("Please enter at least one URL for batch scraping.")

                        # Scheduled Scraping Section
                        st.header("Scheduled Scraping")
                        with st.expander("Schedule New Scraping Job"):
                            schedule_name = st.text_input("Job Name")
                            schedule_url = st.text_input("URL to Scrape")
                            schedule_interval = st.number_input("Interval (hours)", min_value=1, value=24)
                            schedule_content_type = st.selectbox(
                                "Content Type",
                                ['text', 'links', 'images', 'tables', 'article'],
                                key="schedule_content_type"
                            )

                            if st.button("Schedule Job"):
                                if schedule_name and schedule_url:
                                    if scraper.schedule_manager.add_job(
                                            schedule_name,
                                            schedule_url,
                                            schedule_content_type,
                                            schedule_interval
                                    ):
                                        st.success("Job scheduled successfully!")
                                    else:
                                        st.error("Failed to schedule job. Name may already exist.")
                                else:
                                    st.warning("Please provide both job name and URL.")

                            # Display scheduled jobs
                            st.subheader("Current Scheduled Jobs")
                            jobs = scraper.schedule_manager.get_all_jobs()
                            if jobs:
                                for name, job in jobs.items():
                                    with st.expander(f"Job: {name}"):
                                        st.write(f"URL: {job['url']}")
                                        st.write(f"Type: {job['content_type']}")
                                        st.write(f"Interval: {job['interval_hours']} hours")
                                        if job['last_run']:
                                            st.write(f"Last Run: {job['last_run']}")
                                        if job['next_run']:
                                            st.write(f"Next Run: {job['next_run']}")

                                        # Add option to view results
                                        if st.button(f"View Results for {name}"):
                                            results = scraper.schedule_manager.get_job_results(name)
                                            if results:
                                                st.json(results)
                                            else:
                                                st.info("No results available yet.")

                        # History and Analytics Section
                        st.header("History and Analytics")
                        with st.expander("Scraping History"):
                            history = scraper.get_scraping_history()
                            if history:
                                history_df = pd.DataFrame(history)
                                st.dataframe(history_df)

                                # Add export option for history
                                history_format = st.selectbox(
                                    "Export history format",
                                    ['json', 'csv', 'txt'],
                                    key="history_format"
                                )

                                exported_history = scraper.export_history(history_format)
                                st.download_button(
                                    label=f"Export History as {history_format.upper()}",
                                    data=exported_history,
                                    file_name=f"scraping_history_{datetime.now().strftime('%Y%m%d_%H%M%S')}.{history_format}",
                                    mime=f"text/{history_format}"
                                )

                                if st.button("Clear History"):
                                    scraper.clear_history()
                                    st.success("History cleared!")
                                    st.rerun()
                            else:
                                st.info("No scraping history available.")

                        # Performance Analytics
                        st.header("Performance Analytics")
                        with st.expander("View Performance Metrics"):
                            metrics = scraper.get_metrics()

                            # Create metrics visualizations
                            col1, col2, col3 = st.columns(3)
                            with col1:
                                st.metric("Success Rate", f"{metrics['success_rate']:.1f}%")
                            with col2:
                                st.metric("Avg Response Time", f"{metrics['avg_response_time']:.2f}s")
                            with col3:
                                st.metric("Cache Hit Rate", f"{metrics['cache_hit_rate']:.1f}%")

                            # Error distribution
                            if metrics['error_distribution']:
                                st.subheader("Error Distribution")
                                error_df = pd.DataFrame.from_dict(
                                    metrics['error_distribution'],
                                    orient='index',
                                    columns=['Count']
                                )
                                st.bar_chart(error_df)

                    def export_data(data, format):
                        """Export data in various formats"""
                        if format == 'json':
                            return json.dumps(data, indent=2, default=str)
                        elif format == 'csv':
                            if isinstance(data, (list, dict)):
                                if isinstance(data, dict):
                                    data = [data]
                                output = io.StringIO()
                                if data:
                                    # Flatten nested dictionaries
                                    flattened_data = []
                                    for item in data:
                                        flat_item = {}
                                        for key, value in item.items():
                                            if isinstance(value, (dict, list)):
                                                flat_item[key] = json.dumps(value)
                                            else:
                                                flat_item[key] = value
                                        flattened_data.append(flat_item)

                                    writer = csv.DictWriter(output, fieldnames=flattened_data[0].keys())
                                    writer.writeheader()
                                    writer.writerows(flattened_data)
                                return output.getvalue()
                            else:
                                return "Data not suitable for CSV export"
                        elif format == 'txt':
                            if isinstance(data, str):
                                return data
                            else:
                                return str(data)

                    if __name__ == "__main__":
                        main()